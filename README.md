# Morrey's problem in Lean

Morrey's problem (1952) asks whether every rank-one convex integrand `f : ℝ^{d×m} → ℝ` is
quasiconvex, that is, whether convexity along rank-one lines is enough for the integral
`∫ f(∇u)` to be weakly lower semicontinuous. This repository formalizes, in Lean 4 with Mathlib,
three papers on it, each audited on its own:

| Paper | Claim | Formalization |
| --- | --- | --- |
| [Pedregal](Pedregal) (arXiv:1905.06571v5, 2026) | yes for `2 × 2` | the proof fails: Corollary 7.2 is false (refuted in Lean); the rest of the argument is proved; the claim stays open |
| [Šverák](Sverak) (Proc. Roy. Soc. Edinburgh 1992) | no for `d ≥ 3` components, `m ≥ 2` | proved |
| [Cassese](Cassese) (arXiv:2608.03488v3, 2026) | no for `2 × m`, `m ≥ 3`; homogeneous versions | in progress: definitions and bridges to Šverák's |

Each paper's directory holds its library, its Challenge and Solution, its Palomar files
(`comparator.json`, `formalization.yaml`), its routes, and its documents. The papers share
[`Basic/`](Basic) (general mathematics), [`External/`](External) (cited results), [`scripts/`](scripts) (the audit and the
checks) and the build.

```sh
lake exe cache get && lake build
lake env lean scripts/Audit.lean
```

License: Apache-2.0 ([`LICENSE`](LICENSE)).
