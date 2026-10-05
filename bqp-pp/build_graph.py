"""Bounded, dependency-aware Lean workers, intended to run inside Slurm only."""
import concurrent.futures as futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

if not os.environ.get('SLURM_JOB_ID'):
    raise SystemExit('Run this build inside a Slurm allocation.')
root = Path(__file__).resolve().parent
manifest = json.loads((root / 'source-manifest.json').read_text())
modules = manifest['modules']
source_root = root / 'src'
logs = root / 'logs'
logs.mkdir(exist_ok=True)
lean = os.environ['BQP_LEAN']
env = dict(os.environ)
env['LEAN_PATH'] = str(source_root) + ':' + env['LEAN_PATH']
threads = 1
workers = int(os.environ.get('BQP_WORKERS', '32'))
if workers < 1:
    raise SystemExit('BQP_WORKERS must be positive.')
if int(os.environ.get('SLURM_CPUS_PER_TASK', '0')) < workers:
    raise SystemExit(f'This build requires an allocation of at least {workers} CPU cores.')
records = {}
reused = set()
previous = {}
previous_job = None
previous_result = root / 'previous-build-result.json'
previous_manifest = root / 'previous-source-manifest.json'
if previous_result.exists() and previous_manifest.exists():
    old_manifest = json.loads(previous_manifest.read_text())
    if all(old_manifest.get(k) == manifest.get(k) for k in ['lean_version', 'mathlib_rev']):
        old_result = json.loads(previous_result.read_text())
        previous = old_result['modules']
        previous_job = old_result['job_id']
started = time.monotonic()


def try_reuse(name):
    info = modules[name]
    old = previous.get(name)
    source = source_root / info['path']
    output = source.with_suffix('.olean')
    deps = [d for d in info['imports'] if d in modules]
    if not old or old['exit_code'] != 0 or not all(d in reused for d in deps):
        return False
    if old['source_sha256'] != info['sha256'] or not output.exists():
        return False
    if hashlib.sha256(source.read_bytes()).hexdigest() != info['sha256']:
        return False
    if hashlib.sha256(output.read_bytes()).hexdigest() != old.get('olean_sha256'):
        return False
    records[name] = dict(old, reused=True, previous_job_id=previous_job)
    reused.add(name)
    print('REUSE', name, flush=True)
    return True


def save_results(pending):
    (root / 'build-result.json').write_text(json.dumps({
        'job_id': os.environ['SLURM_JOB_ID'], 'workers': workers,
        'threads_per_process': threads, 'modules': records,
        'blocked': sorted(pending), 'seconds': round(time.monotonic() - started, 2),
    }, indent=2) + '\n')


def build(name):
    info = modules[name]
    source = source_root / info['path']
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    if digest != info['sha256']:
        raise RuntimeError('Source hash mismatch: ' + name)
    output = source.with_suffix('.olean')
    command = [lean, '-j', str(threads), '-o', str(output), str(source)]
    print('START', name, flush=True)
    start = time.monotonic()
    with (logs / (name + '.log')).open('w') as log:
        run = subprocess.run(['/usr/bin/time', '-v', '-o', str(logs / (name + '.time'))] + command,
                             cwd=source_root, env=env, stdout=log, stderr=subprocess.STDOUT)
    timing = (logs / (name + '.time')).read_text()
    rss = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', timing)
    result = {'exit_code': run.returncode, 'seconds': round(time.monotonic() - start, 2),
              'source_sha256': digest, 'max_rss_kb': int(rss[1]) if rss else None}
    if run.returncode == 0:
        result['olean_sha256'] = hashlib.sha256(output.read_bytes()).hexdigest()
    print('FINISH', name, json.dumps(result), flush=True)
    return result


# Representative Mathlib import before choosing the parallel memory budget.
pilot = 'Definitions.Def_PvsNP'
if any(d in modules for d in modules[pilot]['imports']):
    raise SystemExit('Pilot unexpectedly has local prerequisites')
if not try_reuse(pilot):
    records[pilot] = build(pilot)
if records[pilot]['exit_code']:
    raise SystemExit('Pilot failed; inspect its log before resubmission.')
if records[pilot]['max_rss_kb']:
    budget_kb = int(os.environ.get('SLURM_MEM_PER_NODE', '49152')) * 1024
    estimated_kb = workers * 1.5 * records[pilot]['max_rss_kb']
    if estimated_kb > budget_kb:
        raise SystemExit(f'{workers}-worker pilot estimate {estimated_kb / 1024**2:.1f} GiB exceeds allocation; request more memory.')
print('WORKERS', workers, 'THREADS_EACH', threads, flush=True)
pending = set(modules) - set(records)
running = {}
with futures.ThreadPoolExecutor(max_workers=workers) as pool:
    while pending or running:
        progress = False
        for name in sorted(pending):
            if len(running) >= workers:
                break
            deps = [d for d in modules[name]['imports'] if d in modules]
            if all(d in records and records[d]['exit_code'] == 0 for d in deps):
                if not try_reuse(name):
                    running[pool.submit(build, name)] = name
                pending.remove(name)
                progress = True
        if not running:
            if progress:
                continue
            break
        done, _ = futures.wait(running, return_when=futures.FIRST_COMPLETED)
        for task in done:
            name = running.pop(task)
            records[name] = task.result()
        save_results(pending)
save_results(pending)
if pending or any(r['exit_code'] for r in records.values()):
    raise SystemExit('Build failed or dependents blocked; inspect build-result.json and logs.')
print('ALL_TARGETS_PASSED', ' '.join(manifest['targets']), flush=True)
