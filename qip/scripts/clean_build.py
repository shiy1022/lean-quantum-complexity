#!/usr/bin/env python3
"""From-scratch build and audit of the qip project.

Refuses to start if `.lake/build` exists, so no project object (qip or the `Baseline` selection of
bqp-pp sources) is reused. The pinned Mathlib checkout under `packagesDir` is used as is. Runs
`scripts/audit.py` (one Lean thread: `lake build ShiQIP`, then every audit file) and writes
`verification/clean-build.json`. Without `SLURM_JOB_ID` the record is labelled as a local clean
build; it is never Sherlock evidence.

    python scripts/clean_build.py
"""
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / '.lake' / 'build'


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    if BUILD.exists():
        sys.exit('refusing to start: .lake/build exists (move it away for a clean build)')
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    start_wall = time.time()
    started = time.monotonic()
    proc = subprocess.run([sys.executable, str(ROOT / 'scripts' / 'audit.py')], cwd=ROOT, env=env,
                          capture_output=True, text=True, encoding='utf-8', errors='replace')
    seconds = round(time.monotonic() - started, 1)
    log = proc.stdout + proc.stderr
    (ROOT / 'verification' / 'clean-build.log').write_text(log, encoding='utf-8', newline='\n')
    oleans = sorted(BUILD.rglob('*.olean'))
    stale = [p.relative_to(ROOT).as_posix() for p in oleans if p.stat().st_mtime < start_wall]
    audit = json.loads((ROOT / 'verification' / 'audit.json').read_text(encoding='utf-8'))
    slurm = os.environ.get('SLURM_JOB_ID')
    reports = audit['axiom_reports']
    result = {
        'kind': ('Slurm job ' + slurm) if slurm else 'local clean build (not Sherlock)',
        'host': platform.platform(),
        'lean': audit['lean'], 'mathlib_rev': audit['mathlib_rev'], 'lean_num_threads': 1,
        'git_head': audit['git_head'],
        'started_unix': round(start_wall), 'seconds': seconds,
        'project_objects_before': 0,
        'project_oleans_built': len(oleans),
        'project_oleans_older_than_start': stale,
        'mathlib_objects': 'reused from the pinned packagesDir checkout (../bqp-pp/.lake/packages)',
        'audit_files': len(reports), 'axiom_reports': sum(len(r) for r in reports.values()),
        'audit_errors': audit['errors'], 'audit_exit_code': proc.returncode,
        'log_sha256': hashlib.sha256(log.encode('utf-8')).hexdigest(),
    }
    (ROOT / 'verification' / 'clean-build.json').write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + '\n', encoding='utf-8', newline='\n')
    print(log.strip().splitlines()[-1] if log.strip() else '(no output)')
    print(f'{len(oleans)} project oleans built, {len(stale)} older than the start, {seconds} s')
    sys.exit(1 if proc.returncode or stale else 0)


if __name__ == '__main__':
    main()
