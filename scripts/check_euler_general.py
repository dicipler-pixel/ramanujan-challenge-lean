#!/usr/bin/env python3
"""Reproduce the independent general Euler-integral edition's proof checks."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

import verify

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification-euler'
MODULE = 'RamanujanChallenge.EulerGeneral'
SOURCE = ROOT / 'RamanujanChallenge/EulerGeneral.lean'


def run(label, args, expect_failure=False):
    print(label, flush=True)
    proc = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    output = proc.stdout + proc.stderr
    (OUT / (label + '.log')).write_text(output)
    if expect_failure:
        if proc.returncode == 0 or 'error: unsolved goals' not in output:
            raise RuntimeError('negative control did not fail mathematically: ' + output)
        if re.search(r'unknown identifier|type mismatch|unexpected token|does not exist', output, re.I):
            raise RuntimeError('negative control failed for an infrastructure/type error')
    elif proc.returncode or 'warning:' in output:
        raise RuntimeError(label + ' failed: ' + output)
    return output


def main():
    OUT.mkdir(exist_ok=True)
    result = OUT / 'report.json'
    result.unlink(missing_ok=True)
    manifest = (ROOT / 'lake-manifest.json').read_bytes()
    config = json.loads((ROOT / 'scripts/config.json').read_text())
    names = verify.theorems_in(SOURCE)
    expected = [n for n in config['expected_names'] if n.startswith('EulerIntegralReview.')]
    if sorted(names) != sorted(expected) or len(names) != 15:
        raise RuntimeError('general Euler declaration inventory changed')
    run('build', ['lake', 'build', MODULE])
    run('strict_source', ['lake', 'env', 'lean', '-DwarningAsError=true', str(SOURCE)])
    run('specializations', ['lake', 'env', 'lean', '-DwarningAsError=true',
                            'review-euler/Specializations.lean'])
    run('kernel_replay', ['lake', 'env', 'leanchecker', MODULE])
    audit = OUT / 'Axioms.lean'
    audit.write_text('import ' + MODULE + '\n' +
                     ''.join('#print axioms ' + name + '\n' for name in names))
    log = run('axioms', ['lake', 'env', 'lean', str(audit)])
    axioms = {}
    for name in names:
        pattern = re.escape("'" + name + "' ") + r'(?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)'
        matches = list(re.finditer(pattern, log))
        if len(matches) != 1:
            raise RuntimeError('missing or duplicate axiom report for ' + name)
        used = sorted(a.strip() for a in (matches[0].group(1) or '').split(',') if a.strip())
        if set(used) - verify.ALLOWED:
            raise RuntimeError('disallowed axioms: ' + name + ' ' + str(used))
        axioms[name] = used
    run('false_normalization', ['lake', 'env', 'lean', 'review-euler/FalseNormalization.lean'], True)
    if manifest != (ROOT / 'lake-manifest.json').read_bytes():
        raise RuntimeError('manifest changed during verification')
    version = run('lean_version', ['lake', 'env', 'lean', '--version']).strip()
    result.write_text(json.dumps({
        'lean': version, 'module': MODULE, 'theorems': len(names),
        'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'manifest_sha256': hashlib.sha256(manifest).hexdigest(),
        'warnings': 0, 'kernel_replay': 'passed', 'specializations': 'passed',
        'negative_control': 'rejected', 'axioms': axioms,
        'axiom_union': sorted({a for used in axioms.values() for a in used}),
    }, indent=2) + '\n')
    print('PASS: 15 theorem audit, strict source, kernel replay, specializations and false control.')


if __name__ == '__main__':
    main()
