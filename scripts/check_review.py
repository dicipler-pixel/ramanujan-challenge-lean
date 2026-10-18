#!/usr/bin/env python3
"""Reproduce the reviewed edition's build, kernel replay and axiom audit."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'


def run(label, args):
    print(label, flush=True)
    with (OUT / f'{label}.log').open('w') as log:
        proc = subprocess.run(args, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if proc.returncode:
        print((OUT / f'{label}.log').read_text())
        raise SystemExit(proc.returncode)


def main():
    OUT.mkdir(exist_ok=True)
    result = OUT / 'review_checks.json'
    result.unlink(missing_ok=True)  # Never leave a stale success report after failure.
    manifest = (ROOT / 'lake-manifest.json').read_bytes()
    run('audit_regressions', [sys.executable, 'scripts/test_verify.py'])
    run('build', ['lake', 'build'])
    config = json.loads((ROOT / 'scripts/config.json').read_text())
    for module in config['modules']:
        run(module['module'] + '_kernel', ['lake', 'env', 'leanchecker', module['module']])
    run('audit', [sys.executable, 'scripts/verify.py'])
    if manifest != (ROOT / 'lake-manifest.json').read_bytes():
        raise SystemExit('dependency manifest changed during verification')
    result.write_text(json.dumps({
        'build': 'passed',
        'kernel_replay': [m['module'] for m in config['modules']],
        'audit': 'passed',
        'audit_regressions': 'passed',
        'manifest_sha256': hashlib.sha256(manifest).hexdigest(),
    }, indent=2) + '\n')
    print('All review checks passed.', flush=True)


if __name__ == '__main__':
    main()
