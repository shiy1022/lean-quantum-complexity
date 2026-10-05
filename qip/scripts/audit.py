#!/usr/bin/env python3
"""Build-and-audit runner for the qip project.

Source-only checks (no Lean is invoked):

  python scripts/audit.py --self-test     # the report parser rejects bad fixtures
  python scripts/audit.py --source-only   # hashes, CRLF, forbidden sorry/admit/axiom

Lean checks build the ShiQIP library with Lake (one Lean thread) and elaborate every
`src/QIP/Audit/*.lean` file freshly, requiring exactly one report per `#print axioms`
request, using only propext / Classical.choice / Quot.sound:

  python scripts/audit.py                 # local check (labelled as such, not Sherlock)
  python scripts/audit.py --require-slurm # refuse to run outside a Slurm allocation

Results go to verification/audit.json. A local run is never Sherlock clean-build evidence.
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
AUDIT_DIR = SRC / 'QIP' / 'Audit'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_VERSION = '4.33.1'
MATHLIB_REV = '0df444a360eaa60ab8c11dca51a86af692955474'
REPORT = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
REQUEST = re.compile(r'^\s*#print\s+axioms\s+(\S+)', re.M)
FORBIDDEN_SOURCE = re.compile(r'\b(sorry|admit|proof_wanted)\b|^\s*axiom\s', re.M)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(text):
    return re.sub(r'--.*', '', re.sub(r'/-.*?-/', '', text, flags=re.S))


def check_reports(source_text, log_text):
    """Return (reports, errors) for one audit file."""
    expected = REQUEST.findall(source_text)
    errors = []
    if not expected:
        errors.append('audit file has no #print axioms request')
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
    for name in found:
        if name not in expected:
            errors.append('unrequested axiom report: ' + name)
    return {n: found[n] for n in expected if n in found}, errors


def self_test():
    src = "#print axioms A\n#print axioms B\n"
    good = "'A' depends on axioms: [propext]\n'B' does not depend on any axioms\n"
    assert check_reports(src, good)[1] == []
    assert any('missing' in e for e in check_reports(src, "'A' depends on axioms: [propext]\n")[1])
    assert any('forbidden' in e for e in check_reports(
        src, good.replace('[propext]', '[propext, sorryAx]'))[1])
    assert any('forbidden' in e for e in check_reports(
        src, good.replace('[propext]', '[propext, ShiQIP.myAxiom]'))[1])
    assert any('duplicate axiom report' in e for e in check_reports(src, good + good)[1])
    assert any('duplicate #print' in e for e in check_reports(src + src, good)[1])
    assert any('no #print' in e for e in check_reports('-- empty\n', '')[1])
    assert any('unrequested' in e for e in check_reports(
        "#print axioms A\n", good)[1])
    # Lake prefixes reports with "info: file:line:col: "; the parser must still find them.
    lake = "info: src/X.lean:3:0: 'A' depends on axioms: [propext]\n" \
           "info: src/X.lean:4:0: 'B' does not depend on any axioms\n"
    assert check_reports(src, lake)[1] == []
    assert FORBIDDEN_SOURCE.search('theorem t : True := by\n  sorry\n')
    assert FORBIDDEN_SOURCE.search('axiom bad : False\n')
    assert not FORBIDDEN_SOURCE.search(strip_comments('-- a sorry in a comment\n'))
    assert not FORBIDDEN_SOURCE.search('-- no sorries here: sorryless\n')
    print('self-test passed')


def source_checks():
    errors = []
    sources = sorted(SRC.rglob('*.lean'))
    hashes = {p.relative_to(SRC).as_posix(): sha256(p) for p in sources}
    for p in sources:
        rel = p.relative_to(SRC).as_posix()
        if b'\r' in p.read_bytes():
            errors.append('CRLF line endings: ' + rel)
        if FORBIDDEN_SOURCE.search(strip_comments(p.read_text(encoding='utf-8'))):
            errors.append('sorry/admit/axiom in source: ' + rel)
    return sources, hashes, errors


def run(cmd):
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, encoding='utf-8',
                          env=env)


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--source-only', action='store_true')
    parser.add_argument('--require-slurm', action='store_true')
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    sources, hashes, errors = source_checks()
    if args.source_only:
        for e in errors:
            print('ERROR', e)
        print(f'{"FAILED" if errors else "PASSED"} (source only): {len(sources)} sources')
        sys.exit(1 if errors else 0)
    slurm = os.environ.get('SLURM_JOB_ID')
    if args.require_slurm and not slurm:
        sys.exit('refusing to compile: no SLURM_JOB_ID (run inside a Sherlock allocation)')
    version = run(['lake', 'env', 'lean', '--version']).stdout.strip()
    if f'version {LEAN_VERSION},' not in version:
        errors.append('unexpected Lean version: ' + version)
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
    revs = {p['name']: p['rev'] for p in manifest['packages']}
    if revs.get('mathlib') != MATHLIB_REV:
        errors.append('unexpected Mathlib revision: ' + str(revs.get('mathlib')))
    started = time.monotonic()
    if not args.skip_build:
        build = run(['lake', 'build', 'ShiQIP'])
        if build.returncode:
            print(build.stdout[-4000:], build.stderr[-4000:])
            errors.append('lake build ShiQIP failed')
        if re.search(r'declaration uses .sorry.', build.stdout + build.stderr):
            errors.append('sorry warning during build')
    audits = {}
    for p in sorted(AUDIT_DIR.glob('*.lean')):
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
        'kind': ('Slurm job ' + slurm) if slurm else 'local check (not a Sherlock clean build)',
        'host': platform.platform(), 'lean': version, 'mathlib_rev': revs.get('mathlib'),
        'lean_num_threads': 1,
        'git_head': run(['git', 'rev-parse', 'HEAD']).stdout.strip(),
        'seconds': round(time.monotonic() - started, 1),
        'source_sha256': hashes, 'axiom_reports': audits, 'errors': errors,
    }
    (ROOT / 'verification' / 'audit.json').write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + '\n', encoding='utf-8', newline='\n')
    for e in errors:
        print('ERROR', e)
    n = sum(len(r) for r in audits.values())
    print(f'{"FAILED" if errors else "PASSED"}: {len(sources)} sources, {len(audits)} audit files, '
          f'{n} axiom reports')
    sys.exit(1 if errors else 0)


if __name__ == '__main__':
    main()
