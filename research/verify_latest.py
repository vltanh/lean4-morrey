#!/usr/bin/env python3
"""Check the saved research payload without rerunning optimization or modifying it.

Default: payload hashes and four exact algebra/certificate checks.
--all: also rerun four floating/high-precision consistency checks.
This is Python verification, not Lean kernel verification.
"""

import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent / "experiments" / "2026-11-21"
EXACT = [
    ("pbeta_threshold", "work_pb/beta2_certificate.py"),
    ("cassese_degeneracy", "work_cassese/exact_degeneracy.py"),
    ("sos_and_dh_parameters", "work_lit/verify_sos_and_dh_parameters.py"),
    ("sverak_control", "work_sos/certify_control.py"),
]
NUMERICAL = [
    ("sos_floating_outputs", "work_sos/validate_outputs.py"),
    ("cassese_saved_fields", "work_cassese/validate_results.py"),
    ("pbeta_high_precision", "work_pb/validate_results.py"),
    ("independent_sos_audit", "work_lit/audit_sos.py"),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--out", type=Path, default=ROOT.parents[1] / "verification" / "2026-11-21")
    parser.add_argument("--timeout", type=int, default=180,
                        help="seconds allowed per verifier; no optimization is rerun")
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((ROOT / "manifest.json").read_text())
    records = manifest["files"]
    for record in records:
        path = ROOT / record["path"]
        assert path.resolve().is_relative_to(ROOT), path
        data = path.read_bytes()
        assert len(data) == record["size"], path
        assert hashlib.sha256(data).hexdigest() == record["sha256"], path
    packages = {}
    for name in ("numpy", "scipy", "sympy", "mpmath", "cvxpy", "clarabel"):
        try:
            packages[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            packages[name] = None
    result = {
        "scope": "Saved artifact verification; no search rerun and no Lean build",
        "payload_files_checked": len(records),
        "payload_hashes_match": True,
        "python": platform.python_version(),
        "packages": packages,
        "checks": [],
    }
    checks = EXACT + (NUMERICAL if args.all else [])
    env = dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1",
               MKL_NUM_THREADS="1", PYTHONDONTWRITEBYTECODE="1")
    # Several original validators write output beside their input. Isolating them
    # preserves all historical result files and their recorded hashes.
    with tempfile.TemporaryDirectory(prefix="morrey-saved-checks-") as folder:
        working = Path(folder)
        for record in records:
            relative = Path(record["path"])
            (working / relative).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, working / relative)
        for name, script in checks:
            start = time.monotonic()
            try:
                proc = subprocess.run(
                    [sys.executable, script], cwd=working, env=env,
                    capture_output=True, text=True, timeout=args.timeout,
                )
                code, log = proc.returncode, proc.stdout + proc.stderr
            except subprocess.TimeoutExpired as exc:
                code, log = 124, "Verifier exceeded the per-check timeout.\n"
                for value in (exc.stdout, exc.stderr):
                    if value:
                        log += value.decode() if isinstance(value, bytes) else value
            (out / (name + ".log")).write_text(log)
            row = {
                "name": name,
                "script": script,
                "evidence": "exact Python algebra/certificate" if (name, script) in EXACT
                            else "numerical consistency check",
                "exit_code": code,
                "elapsed_seconds": round(time.monotonic() - start, 3),
                "log": name + ".log",
            }
            result["checks"].append(row)
            (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
            print(f"{name}: exit {code}", flush=True)
    failed = [x["name"] for x in result["checks"] if x["exit_code"]]
    print(f"Verified {len(records)} payload hashes; {len(checks)-len(failed)}/{len(checks)} checks passed.")
    return bool(failed)


if __name__ == "__main__":
    sys.exit(main())
