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
    build_log = (OUT / 'build.log').read_text()
    if 'warning' in build_log or 'error' in build_log:
        print(build_log)
        raise SystemExit('lake build reported warnings or errors')
    # Instances of the general Euler integral (negative a and x, singular endpoints, the 2.1
    # family), compiled with warnings as errors.
    run('euler_specializations',
        ['lake', 'env', 'lean', '-DwarningAsError=true', 'checks/EulerSpecializations.lean'])
    config = json.loads((ROOT / 'scripts/config.json').read_text())
    for module in config['modules']:
        run(module['module'] + '_kernel', ['lake', 'env', 'leanchecker', module['module']])
    run('audit', [sys.executable, 'scripts/verify.py'])
    # Mathlib's style checks: the standard linter set on every module, the declaration
    # linters (#lint), and the text-based lint-style.
    for module in config['modules']:
        run(module['module'] + '_standard_lint',
            ['lake', 'env', 'lean', '-Dlinter.mathlibStandardSet=true', module['path']])
        if 'warning' in (OUT / f"{module['module']}_standard_lint.log").read_text():
            print((OUT / f"{module['module']}_standard_lint.log").read_text())
            raise SystemExit(f"standard linter warnings in {module['module']}")
    lint = OUT / 'DeclarationLint.lean'
    lint.write_text(''.join(f'import {m}\n' for m in config['root_imports'])
                    + 'import Mathlib.Tactic.Linter\n#lint in RamanujanChallenge\n')
    run('declaration_lint', ['lake', 'env', 'lean', str(lint.relative_to(ROOT))])
    if 'All linting checks passed!' not in (OUT / 'declaration_lint.log').read_text():
        print((OUT / 'declaration_lint.log').read_text())
        raise SystemExit('#lint reported problems')
    # Build the lint-style executable first, in its own log: on a fresh machine `lake exe`
    # would otherwise print its build progress into the lint report, which must be empty.
    run('lint_style_build', ['lake', 'build', 'lint-style'])
    run('lint_style', ['lake', 'exe', 'lint-style'] + config['root_imports'])
    if (OUT / 'lint_style.log').read_text().strip():
        print((OUT / 'lint_style.log').read_text())
        raise SystemExit('lint-style reported problems')
    if manifest != (ROOT / 'lake-manifest.json').read_bytes():
        raise SystemExit('dependency manifest changed during verification')
    result.write_text(json.dumps({
        'build': 'passed',
        'kernel_replay': [m['module'] for m in config['modules']],
        'audit': 'passed',
        'standard_lint': 'passed',
        'declaration_lint': 'passed',
        'lint_style': 'passed',
        'audit_regressions': 'passed',
        'euler_specializations': 'passed',
        'manifest_sha256': hashlib.sha256(manifest).hexdigest(),
    }, indent=2) + '\n')
    print('All review checks passed.', flush=True)


if __name__ == '__main__':
    main()
