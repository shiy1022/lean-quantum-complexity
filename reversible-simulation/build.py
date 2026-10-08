"""Source-matched clean DAG build, restricted to an allocated compute node."""
import concurrent.futures as futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

root = Path(__file__).resolve().parent
if not os.environ.get('SLURM_JOB_ID'):
    raise SystemExit('A Slurm compute allocation is required.')
manifest = json.loads((root / 'manifest.json').read_text())
modules = manifest['modules']
workers = int(os.environ.get('REV_WORKERS', '3'))
if workers < 2 or workers > int(os.environ['SLURM_CPUS_PER_TASK']):
    raise SystemExit('Parallel worker count must fit the allocation.')
lean = os.environ['REV_LEAN']
env = dict(os.environ)
env['LEAN_PATH'] = str(root / 'src') + ':' + env['LEAN_PATH']
logs = root / 'logs'
logs.mkdir(exist_ok=True)
records = {}
started = time.monotonic()

def build(name):
    info = modules[name]
    source = root / 'src' / info['path']
    sha = hashlib.sha256(source.read_bytes()).hexdigest()
    if sha != info['sha256']:
        raise RuntimeError('Source mismatch: ' + name)
    start = time.monotonic()
    print('START', name, flush=True)
    with (logs / (name + '.log')).open('w') as log:
        run = subprocess.run(['/usr/bin/time', '-v', '-o', str(logs / (name + '.time')),
            lean, '-j', '1', '-o', str(source.with_suffix('.olean')), str(source)],
            cwd=root / 'src', env=env, stdout=log, stderr=subprocess.STDOUT)
    timing = (logs / (name + '.time')).read_text()
    match = re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)', timing)
    record = dict(exit_code=run.returncode, source_sha256=sha,
        seconds=round(time.monotonic()-start, 2), max_rss_kb=int(match[1]) if match else None)
    if run.returncode == 0:
        record['olean_sha256'] = hashlib.sha256(source.with_suffix('.olean').read_bytes()).hexdigest()
    print('FINISH', name, json.dumps(record), flush=True)
    return record

def save(pending):
    (root / 'result.json').write_text(json.dumps(dict(job_id=os.environ['SLURM_JOB_ID'],
        workers=workers, threads_per_process=1, modules=records, blocked=sorted(pending),
        seconds=round(time.monotonic()-started, 2)), indent=2)+'\n')

pilot = 'ReversibleCore'
records[pilot] = build(pilot)
if records[pilot]['exit_code']:
    save(set(modules)-set(records))
    raise SystemExit('Pilot failed; inspect the proof log.')
memory_kb = int(os.environ['SLURM_MEM_PER_NODE']) * 1024
if not records[pilot]['max_rss_kb'] or workers * 1.5 * records[pilot]['max_rss_kb'] > memory_kb:
    save(set(modules)-set(records))
    raise SystemExit('Pilot memory estimate does not fit the parallel allocation.')
pending = set(modules)-set(records)
running = {}
with futures.ThreadPoolExecutor(max_workers=workers) as pool:
    while pending or running:
        for name in sorted(pending):
            if len(running) >= workers:
                break
            dependencies = [d for d in modules[name]['imports'] if d in modules]
            if all(d in records and records[d]['exit_code'] == 0 for d in dependencies):
                running[pool.submit(build, name)] = name
                pending.remove(name)
        if not running:
            break
        done, _ = futures.wait(running, return_when=futures.FIRST_COMPLETED)
        for job in done:
            records[running.pop(job)] = job.result()
        save(pending)
save(pending)
if pending or any(r['exit_code'] for r in records.values()):
    raise SystemExit('Failed proofs or blocked imports; inspect result.json.')
print('ALL_MODULES_PASSED', flush=True)
