#!/usr/bin/env python3
"""Write or check bqp-pspace/source-manifest.json.

Records every new module (path, sha256, imports), the baseline modules it imports (with the
hashes published in bqp-pp/source-manifest.json), pinned versions and the audit targets.

  python scripts/manifest.py          # write
  python scripts/manifest.py --check  # verify sources and baseline against the manifest
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'src'
BASE = ROOT.parent / 'bqp-pp'
IMPORT = re.compile(r'^import\s+(\S+)', re.M)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_name(path):
    return '.'.join(path.relative_to(SRC).with_suffix('').parts)


def strip(name):
    return name[1:-1] if name.startswith('«') and name.endswith('»') else name


def build():
    base = json.loads((BASE / 'source-manifest.json').read_text(encoding='utf-8'))
    modules = {}
    for p in sorted(SRC.rglob('*.lean')):
        imports = [strip(i) for i in IMPORT.findall(p.read_text(encoding='utf-8'))]
        modules[module_name(p)] = {'path': p.relative_to(SRC).as_posix(), 'sha256': sha256(p),
                                   'imports': imports}
    # Baseline closure actually imported, transitively.
    seen, stack = set(), [i for m in modules.values() for i in m['imports'] if i in base['modules']]
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        stack += [i for i in base['modules'][n]['imports'] if i in base['modules']]
    baseline = {n: {'path': base['modules'][n]['path'], 'sha256': base['modules'][n]['sha256']}
                for n in sorted(seen)}
    return {
        'lean_version': '4.33.1',
        'mathlib_rev': '0df444a360eaa60ab8c11dca51a86af692955474',
        'endpoints': ['ShiSpace.pp_subset_pspace', 'ShiBQP.bqp_subset_pspace'],
        'targets': sorted(n for n in modules if n.startswith('Audit.')),
        'modules': modules,
        'baseline_modules': baseline,
    }


def check(manifest):
    current = build()
    errors = []
    for key in ['lean_version', 'mathlib_rev', 'endpoints', 'targets']:
        if manifest[key] != current[key]:
            errors.append(f'{key} differs')
    if set(manifest['modules']) != set(current['modules']):
        errors.append('module set differs: ' + str(set(manifest['modules']) ^ set(current['modules'])))
    for n, info in manifest['modules'].items():
        if n in current['modules'] and info != current['modules'][n]:
            errors.append('changed module: ' + n)
    for n, info in manifest['baseline_modules'].items():
        if sha256(BASE / 'src' / info['path']) != info['sha256']:
            errors.append('baseline source changed: ' + n)
    # import closure and acyclicity over new modules
    mods = manifest['modules']
    state = {}

    def visit(n):
        if state.get(n) == 1:
            errors.append('import cycle at ' + n)
            return
        if state.get(n) == 2:
            return
        state[n] = 1
        for i in mods[n]['imports']:
            if i in mods:
                visit(i)
            elif i not in manifest['baseline_modules'] and not i.startswith('Mathlib'):
                errors.append(f'{n} imports unknown module {i}')
        state[n] = 2

    for n in mods:
        visit(n)
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = ROOT / 'source-manifest.json'
    if args.check:
        errors = check(json.loads(path.read_text(encoding='utf-8')))
        for e in errors:
            print('ERROR', e)
        print('FAILED' if errors else 'Manifest verified')
        sys.exit(1 if errors else 0)
    m = build()
    path.write_text(json.dumps(m, indent=2, ensure_ascii=False) + '\n', encoding='utf-8',
                    newline='\n')
    print(f"Wrote {len(m['modules'])} modules, {len(m['baseline_modules'])} baseline imports")


if __name__ == '__main__':
    main()
