# Reproducing the research evidence

This guide covers the saved 21 November 2026 counterexample searches. Earlier
certificates are indexed in the [ledger](LEDGER.md). For the original Lean
libraries, use the [repository build instructions](../../README.md#layout-and-building).

## 1. What was imported

The complete earlier-plus-latest source inventory can be checked without external packages:

```sh
python3 research/verify_inventory.py
```

It checks 139 distinct payloads from 36 source artifacts, including 53 historical files.
This verifies preservation, not mathematical correctness.

[`research/experiments/2026-11-21/`](../../research/experiments/2026-11-21/) contains
all 86 files of `morrey_counterexample_search_2026_11_21.zip`, byte for byte.
The source archive SHA256 is
`ba1f63d54f65e1dd297e03ed3a9b4f6b18228802d693f6a781ecce09c4b99397`.
Its original [manifest](../../research/experiments/2026-11-21/manifest.json)
records size and SHA256 for the 85 payload files other than the manifest itself.

No path or mathematical code changes were needed: scripts already use sibling
imports and paths relative to their containing directory. The only additions
are the external [verification wrapper](../../research/verify_latest.py), its
[verification record](../../research/verification/2026-11-21/results.json), and
the ledger documentation. The wrapper copies the payload into a temporary
directory before executing validators because some original scripts write
their reports next to their inputs. The archived observations remain intact.

## 2. Fast verification; no optimization rerun

From the repository root:

```sh
python3 -m venv .venv-research
. .venv-research/bin/activate
python -m pip install -r research/experiments/2026-11-21/requirements.txt
python research/verify_latest.py --all --out /tmp/morrey-verification
```

The pinned environment is Python 3.12.14 with NumPy 2.3.5, SciPy 1.17.0,
SymPy 1.14.0, mpmath 1.3.0, CVXPY 1.9.3 and Clarabel 0.11.1. Pinning these
versions supports reproducibility; numerical solver trajectories can still
depend on the platform and linear algebra implementation. No solver is invoked
by the saved-output checks, although some imports require CVXPY.

The wrapper verifies payload hashes before running anything. Without `--all`,
it runs only the four exact algebra/certificate checks below. Each verifier has
a 180-second timeout, configurable by `--timeout`; no search is launched.
It exits nonzero if a command fails, and records individual exit codes and logs.

| Check | Evidence and meaning |
| --- | --- |
| `pbeta_threshold` | Exact SymPy square-completion, principal-minor and asymptotic identities for the sharp `β = 2` boundary. The continuity/Sylvester argument is explained in the branch README. |
| `cassese_degeneracy` | Exact zero-polynomial and determinant-square identities; exact generator ranks for five planes. |
| `sos_and_dh_parameters` | Exact `Pβ` SOS identity modulo `det H`, eigenvalues and parameters for the DH candidates. Published rank-one convexity criteria are cited in the branch report. |
| `sverak_control` | Integer/rational coefficient identity, exact positive-definite LDL check and exact negative integral for the saved **`3 × 2`** control. |
| `sos_floating_outputs` (`--all`) | Reconstructs each saved Gram output with its recorded monomial ordering; recomputes floating identity residuals and mean-gradient, determinant and variance constraints. |
| `cassese_saved_fields` (`--all`) | Independent finer-grid evaluation in original ambient coordinates for all 84 saved inherited-family fields. |
| `pbeta_high_precision` (`--all`) | Recomputes ten selected cases with 60 digits, newly minimized bases and direct energy evaluation. |
| `independent_sos_audit` (`--all`) | Independent normalized-field derivative checks and 30 exact physical-Hessian evaluations of the higher-dimensional control. |

All eight passed in this PR's consolidation run. The machine-readable result
and stdout/stderr logs are in
[`research/verification/2026-11-21/`](../../research/verification/2026-11-21/).
Passing a numerical consistency check does not turn its input into an exact
certificate. No Lean build or optimization campaign was rerun for this import.

The `3 × 2` certificate can also be checked without installing any numerical
package, using only the Python standard library. Make a working copy first
because its verifier writes an output JSON file:

```sh
cp -R research/experiments/2026-11-21 /tmp/morrey-control-check
python3 /tmp/morrey-control-check/work_sos/certify_control.py
```

## 3. Repeating a search campaign

Use a fresh working copy so the saved evidence is not overwritten:

```sh
cp -R research/experiments/2026-11-21 /tmp/morrey-search-rerun
cd /tmp/morrey-search-rerun
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
```

Then follow the branch-specific reproduction commands:

| Branch | Instructions | Main outputs |
| --- | --- | --- |
| Sharp `Pβ`, Fourier and finite elements | [`work_pb/README.md`](../../research/experiments/2026-11-21/work_pb/README.md#files-and-reproduction) | Four result JSON files with every field, base, optimizer status and gap; 60-digit audit. |
| DH anisotropic energies | [`work_lit/README.md`](../../research/experiments/2026-11-21/work_lit/README.md#reproduce) | Results for joint, fixed-base and conditioned-base searches; best fields. |
| Cassese pullbacks and SOS penalties | [`work_cassese/README.md`](../../research/experiments/2026-11-21/work_cassese/README.md#reproduction) | All inherited-family fields, altered-penalty SDP diagnostics and exact degeneracy identities. |
| General polynomial SOS | [`work_sos/README.md`](../../research/experiments/2026-11-21/work_sos/README.md#reproduce-from-the-archive-root) | Degree 4/6 coefficient vectors, Gram matrices, nodal fields and every alternating step. |

Searches have fixed seeds but no finite run is exhaustive. Record the seed,
dependencies, solver status, field normalization, polynomial basis ordering,
base matrix and barrier coefficient with any new result. Compare the actual
Jensen gap separately from any regularized objective.

## 4. Interpretation and promotion rules

- The sign convention here is `mean f(F+Dφ) − f(F)`; negative is a violation.
  Some earlier polynomial notes/checkers use the opposite sign. Translate the
  definition before comparing outputs.
- Use saved `zexponents` and `exponents` to interpret NPZ data. The first
  quartic SOS run predates the later monomial ordering.
- `optimal` or `optimal_inaccurate` is a floating solver status, not a proof.
  Exact coefficient matching and PSD certification remain separate gates.
- Retain failed and excluded records. In particular, the two Cassese
  `penalty_*_best.npz` files are quarantined records: one fails the Gram test,
  the other is a zero integrand. Their filename does not confer validity.
- A positive local optimum does not prove quasiconvexity; a negative sampled
  candidate does not prove global rank-one convexity. Determinant compatibility
  of an abstract measure alone does not make it a gradient Young measure.
- A new negative candidate should be recomputed independently, reconstructed
  rationally where possible, and paired with an exact or rigorously bounded
  global rank-one-convexity certificate and an admissible gradient witness.
  Then establish the periodic-to-zero-boundary bridge for the intended theorem
  and formalize the complete argument. The [roadmap](ROADMAP.md) sets those gates.

## 5. Historical checks replayed in the consolidation

Ten earlier algebra/combinatorial checkers also passed. Together with the eight latest checks,
this is **18 successful verification commands: 14 exact algebra/certificate checks and four
floating/high-precision consistency checks**. Exact finite calculations do not verify every
analytic bridge or universal quantifier in their accompanying hand arguments.

| Checks | Recorded evidence |
| --- | --- |
| Universal level-one mold; all-level finite stencil reduction; explicit level-two obstruction and weight neighborhood; rational polynomial/SOS sanity pipeline | [Four-check record](../../research/verification/2026-11-21/history/results.json) and adjacent logs, with source hashes and scope qualifications. |
| 32-atom quartic certificate; cubic rigidity; rank-one-affine kernel/moment witness; coefficient-neighborhood constants; quartic orbit basis; harmonic identities | [Six-check record](../../research/verification/2026-11-21/history_additional/results.json) and adjacent logs. |

For portable historical scripts, copy the archive before running:

```sh
cp -R research/archive/files /tmp/morrey-history-check
cd /tmp/morrey-history-check
python3 morrey_l1_mold_certificate.py
python3 morrey_all_levels_uniform_obstruction.py
python3 morrey_level2_uniform_fixedpoint_obstruction.py
python3 morrey_polynomial_certificate.py
python3 morrey_verify_quartic_l2_certificate.py
python3 morrey_cubic_rigidity.py
python3 morrey_rankone_kernel_exact_check.py
python3 morrey_global_quartic_open_ball_verify.py
```

The orbit-basis and harmonic verifiers contain historical `/mnt/data/` paths. For their replays,
only that prefix was replaced by the temporary directory in temporary script copies; the original
scripts and data remain unchanged in the archive. The relocation is recorded in the six-check
JSON. The old open-neighborhood generator has a similar path requirement and writes a JSON;
it was not among these ten replays.

`morrey_false_quartic_exact_witness.py` additionally needs the missing discovery artifact
`morrey_four_wave_exchange_last.npz`. Its historical negative LH value is recorded in H27, but
that calculation was **not replayed**. Do not present this script alone as a self-contained
certificate or silently substitute a different candidate.

The curated Markdown tables and local links, Python syntax, source inventory and existing
Challenge-definition synchronization were checked. Lean compilation, axiom/route audits and
Comparator were not run locally for this documentation-and-research import; no Lean file changes
are part of it.

## 6. Completion-audit checks

The new exact controls are separate from the 139 immutable historical payloads. Run:

```sh
python3 research/verify_audit.py --out /tmp/morrey-audit-check
```

The wrapper copies the audit package to a temporary directory, runs six exact commands,
checks that regenerated outputs match their saved bytes, and records logs and input hashes.
It requires SymPy for the P₂ SOS and Schur-expansion identities; the certificate and base
checks use only the standard library. No optimization is run.

The [audit package](../../research/audit/README.md) documents both certificate formats and the
quadratic regression controls. [Recorded verification](../../research/verification/completion_audit/results.json)
contains six passing commands, including both positive certificate formats and six malformed
certificate rejections. These checks do not prove the unresolved all-field inequality, discover
a counterexample, or run Lean. Upstream Lean CI status is pinned in
[FORMAL_STATUS.md](FORMAL_STATUS.md).
