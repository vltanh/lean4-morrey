#!/usr/bin/env python3
"""Replay the completion audit's exact checks in a temporary copy.

No optimization is run. The saved research inputs and outputs are not modified.
SymPy is needed only for the two symbolic polynomial identities.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent / 'audit'
    args.out.mkdir(parents=True, exist_ok=True)
    commands = [
        ('sphere_controls', ['sphere_control.py']),
        ('sphere_certificate', ['sphere_certificate.py', 'sphere_control_certificate.json']),
        ('norm_certificate', ['sphere_certificate.py', 'norm_control_certificate.json']),
        ('exact_base', ['exact_base.py']),
        ('pbeta_sos', ['pbeta_exact_sos.py']),
        ('pbeta_schur', ['pbeta_schur_reduction_check.py']),
    ]
    result = {
        'scope': 'Exact audit controls and identities only; no planar counterexample, search rerun or Lean build.',
        'python': sys.version.split()[0],
        'inputs_sha256': {p.name: sha(p) for p in sorted(source.iterdir()) if p.is_file()},
        'checks': [],
    }
    with tempfile.TemporaryDirectory(prefix='morrey-completion-audit-') as tmp:
        work = Path(tmp) / 'audit'
        shutil.copytree(source, work, ignore=shutil.ignore_patterns('__pycache__'))
        for name, command in commands:
            try:
                run = subprocess.run([sys.executable, *command], cwd=work,
                                     capture_output=True, text=True, timeout=60)
                status = run.returncode
                output = run.stdout + run.stderr
            except subprocess.TimeoutExpired as error:
                status = 124
                output = str(error)
            (args.out / (name + '.log')).write_text(output)
            result['checks'].append({'name': name, 'command': ['python3', *command],
                                     'exit_code': status, 'log': name + '.log'})
            print(f'{name}: {"PASS" if status == 0 else "FAIL"}')
        regenerated = [
            'sphere_control_certificate.json', 'norm_control_certificate.json',
            'sphere_control_results.json', 'exact_base_controls.json', 'pbeta_exact_sos.json',
        ]
        result['saved_output_matches'] = {
            name: (source / name).read_bytes() == (work / name).read_bytes()
            for name in regenerated
        }
    result['passed'] = (all(c['exit_code'] == 0 for c in result['checks'])
                        and all(result['saved_output_matches'].values()))
    (args.out / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    if not result['passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
