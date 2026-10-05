#!/usr/bin/env python3
"""Local (non-Sherlock) build-and-audit runner for bqp-pspace.

Builds the ShiSpace library with Lake, elaborates every `src/Audit/*.lean` file, and checks
that each `#print axioms` request has exactly one report using only the allowed axioms.
Records source hashes and results in `verification/local-audit.json`. Evidence produced here
is a local Windows/Linux check, not a Sherlock clean build.

  python scripts/audit.py              # build + audit
  python scripts/audit.py --self-test  # check that the parser rejects bad fixtures
"""
import argparse
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'src'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_VERSION = '4.33.1'
MATHLIB_REV = '0df444a360eaa60ab8c11dca51a86af692955474'
REPORT = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M)
REQUEST = re.compile(r'^\s*#print\s+axioms\s+(\S+)', re.M)
FORBIDDEN_SOURCE = re.compile(r'\b(sorry|admit|proof_wanted)\b|^\s*axiom\s', re.M)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_reports(source_text, log_text):
    """Return (reports, errors) for one audit file."""
    expected = REQUEST.findall(source_text)
    errors = []
    if len(expected) != len(set(expected)):
        errors.append('duplicate #print axioms request')
    found = {}
    for name, axioms in REPORT.findall(log_text):
        if name in found:
            errors.append('duplicate axiom report: ' + name)
        found[name] = sorted(a.strip() for a in axioms.split(',') if a.strip())
    for name in expected:
        if name not in found:
            errors.append('missing axiom report: ' + name)
        elif not set(found[name]) <= ALLOWED:
            errors.append(f'forbidden axioms in {name}: {sorted(set(found[name]) - ALLOWED)}')
    return {n: found[n] for n in expected if n in found}, errors


def self_test():
    src = "#print axioms A\n#print axioms B\n"
    good = "'A' depends on axioms: [propext]\n'B' does not depend on any axioms\n"
    assert check_reports(src, good)[1] == []
    assert any('missing' in e for e in check_reports(src, "'A' depends on axioms: [propext]\n")[1])
    assert any('forbidden' in e for e in check_reports(
        src, good.replace('[propext]', '[propext, sorryAx]'))[1])
    assert any('duplicate axiom report' in e for e in check_reports(src, good + good)[1])
    assert FORBIDDEN_SOURCE.search('theorem t : True := by\n  sorry\n')
    assert FORBIDDEN_SOURCE.search('axiom bad : False\n')
    assert not FORBIDDEN_SOURCE.search('-- no sorries here: sorryless\n')
    print('self-test passed')


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, encoding='utf-8', **kw)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    errors = []
    version = run(['lake', 'env', 'lean', '--version']).stdout.strip()
    if f'version {LEAN_VERSION},' not in version:
        errors.append('unexpected Lean version: ' + version)
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    revs = {p['name']: p['rev'] for p in manifest['packages']}
    if revs.get('mathlib') != MATHLIB_REV:
        errors.append('unexpected Mathlib revision: ' + str(revs.get('mathlib')))
    sources = sorted(SRC.rglob('*.lean'))
    hashes = {p.relative_to(SRC).as_posix(): sha256(p) for p in sources}
    for p in sources:
        text = p.read_text(encoding='utf-8')
        if b'\r' in p.read_bytes():
            errors.append('CRLF line endings: ' + p.relative_to(SRC).as_posix())
        if FORBIDDEN_SOURCE.search(re.sub(r'--.*', '', re.sub(r'/-.*?-/', '', text, flags=re.S))):
            errors.append('sorry/admit/axiom in source: ' + p.relative_to(SRC).as_posix())
    started = time.monotonic()
    if not args.skip_build:
        build = run(['lake', 'build', 'ShiSpace'])
        if build.returncode:
            print(build.stdout[-4000:], build.stderr[-4000:])
            errors.append('lake build ShiSpace failed')
    audits = {}
    for p in sorted((SRC / 'Audit').glob('*.lean')):
        rel = p.relative_to(SRC).as_posix()
        out = run(['lake', 'env', 'lean', str(p)])
        log = out.stdout + out.stderr
        if out.returncode:
            errors.append(f'audit failed to compile: {rel}\n{log[-3000:]}')
        if re.search(r'declaration uses .sorry.', log):
            errors.append('sorry warning in audit: ' + rel)
        reports, errs = check_reports(p.read_text(encoding='utf-8'), log)
        errors += [f'{rel}: {e}' for e in errs]
        audits[rel] = reports
    result = {
        'kind': 'local check (not a Sherlock clean build)',
        'host': platform.platform(), 'lean': version, 'mathlib_rev': revs.get('mathlib'),
        'git_head': run(['git', 'rev-parse', 'HEAD']).stdout.strip(),
        'seconds': round(time.monotonic() - started, 1),
        'source_sha256': hashes, 'axiom_reports': audits, 'errors': errors,
    }
    (ROOT / 'verification' / 'local-audit.json').write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + '\n', encoding='utf-8', newline='\n')
    for e in errors:
        print('ERROR', e)
    n = sum(len(r) for r in audits.values())
    print(f'{"FAILED" if errors else "PASSED"}: {len(sources)} sources, {len(audits)} audit files, {n} axiom reports')
    sys.exit(1 if errors else 0)


if __name__ == '__main__':
    main()
