# Positive-filling joint optimization and exact controls

See the [hand proof](../../../docs/research/IWANIEC_MORREY_DEGREE_FREE_FINITE_FILLINGS.md). This is the practical finite control, not an implementation of the enormous complete degree-free sample net. The three source blobs and compressed proof match executed local files byte-for-byte. Numerical discovery may select different zero-gap incumbents.

From repository root (NumPy/SciPy required):

~~~sh
python3 research/audit/positive_filling_enumerate.py --input research/experiments/2026-11-24-joint-fillings/joint_small_input.json
python3 research/audit/positive_filling_enumerate.py --input research/experiments/2026-11-24-joint-fillings/joint_four_input.json --max-states 4000
gzip -dc research/experiments/2026-11-24-joint-fillings/joint_small_proof.json.gz > /tmp/morrey-joint-proof.json
python3 research/audit/joint_filling_certify.py --verify /tmp/morrey-joint-proof.json
python3 research/audit/joint_positive_filling.py --verify research/experiments/2026-11-24-joint-fillings/joint_small_candidate.json
python3 research/audit/joint_positive_filling.py --verify research/experiments/2026-11-24-joint-fillings/joint_four_candidate.json
~~~

Expected exact results: 32/32 and 1142/1142 fillings certified for every RC energy by rank-one merges. Saved proof tree has 60 branches and 61 lower leaves, all exact bounds zero for the finite square-factor cone. Both saved candidates have nonnegative repaired gaps. The 30-second larger MILP timed out; it supplies no lower-bound certificate. The exact enumeration subsequently establishes the finite geometry result for all RC energies. A separate 20-triangle generic merge attempt timed out after 25 seconds, without a completed experiment.

Proof SHA-256: 341b2e2c2f6e77da6ed9a7e0da4c5d59e92db158aa6618eba4b8d9643d53551c. No global vertex bound, universal merge theorem or new Lean proof.
