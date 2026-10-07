#!/usr/bin/env python3
"""Write or check qip/source-manifest.json. Source-only: never invokes Lean.

Records every new module (path, sha256, imports), the baseline modules it imports transitively
(with the hashes published in bqp-pp/source-manifest.json), pinned versions, the Lake roots of
the read-only Baseline library, and the audit targets. The check also re-verifies the source
manifests of the two existing projects, bqp-pp and bqp-pspace, so that the existing work is
confirmed byte-for-byte unchanged.

  python scripts/manifest.py              # write
  python scripts/manifest.py --check      # verify
  python scripts/manifest.py --self-test  # the checker rejects a tampered manifest
"""
import argparse
import copy
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'src'
REPO = ROOT.parent
BASE = REPO / 'bqp-pp'
SPACE = REPO / 'bqp-pspace'
IMPORT = re.compile(r'^import\s+(\S+)', re.M)
LAKE_ROOTS = re.compile(r'roots\s*=\s*\[(.*?)\]', re.S)
LEAN_VERSION = '4.33.1'
MATHLIB_REV = '0df444a360eaa60ab8c11dca51a86af692955474'


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_name(path):
    return '.'.join(path.relative_to(SRC).with_suffix('').parts)


def strip(name):
    return name[1:-1] if name.startswith('«') and name.endswith('»') else name


def lake_baseline_roots():
    text = (ROOT / 'lakefile.toml').read_text(encoding='utf-8')
    block = LAKE_ROOTS.search(text).group(1)
    return sorted(strip(r) for r in re.findall(r'"([^"]+)"', block))


def build():
    base = json.loads((BASE / 'source-manifest.json').read_text(encoding='utf-8'))
    modules = {}
    for p in sorted(SRC.rglob('*.lean')):
        imports = [strip(i) for i in IMPORT.findall(p.read_text(encoding='utf-8'))]
        modules[module_name(p)] = {'path': p.relative_to(SRC).as_posix(), 'sha256': sha256(p),
                                   'imports': imports}
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
        'lean_version': LEAN_VERSION,
        'mathlib_rev': MATHLIB_REV,
        'endpoint': 'ShiQIP.qip_eq_qip3',
        'baseline_lake_roots': lake_baseline_roots(),
        'targets': sorted(n for n in modules if n.startswith('QIP.Audit.')),
        'modules': modules,
        'baseline_modules': baseline,
    }


def check_existing_projects():
    """Re-verify the published source hashes of bqp-pp and bqp-pspace (source only)."""
    errors = []
    for project in (BASE, SPACE):
        m = json.loads((project / 'source-manifest.json').read_text(encoding='utf-8'))
        actual = {p.relative_to(project / 'src').as_posix()
                  for p in (project / 'src').rglob('*.lean')}
        listed = {info['path'] for info in m['modules'].values()}
        if actual != listed:
            errors.append(f'{project.name}: source set differs from its manifest')
        for name, info in m['modules'].items():
            if sha256(project / 'src' / info['path']) != info['sha256']:
                errors.append(f'{project.name}: changed source {name}')
    return errors


def check(manifest):
    current = build()
    errors = []
    for key in ['lean_version', 'mathlib_rev', 'endpoint', 'baseline_lake_roots', 'targets']:
        if manifest[key] != current[key]:
            errors.append(f'{key} differs')
    base = json.loads((BASE / 'source-manifest.json').read_text(encoding='utf-8'))
    for r in manifest['baseline_lake_roots']:
        if r not in base['modules']:
            errors.append('Baseline Lake root is not a published bqp-pp module: ' + r)
    if set(manifest['modules']) != set(current['modules']):
        errors.append('module set differs: ' + str(set(manifest['modules']) ^ set(current['modules'])))
    for n, info in manifest['modules'].items():
        if n in current['modules'] and info != current['modules'][n]:
            errors.append('changed module: ' + n)
    for n, info in manifest['baseline_modules'].items():
        if sha256(BASE / 'src' / info['path']) != info['sha256']:
            errors.append('baseline source changed: ' + n)
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
            elif i in manifest['baseline_modules']:
                if i not in manifest['baseline_lake_roots']:
                    errors.append(f'{n} imports baseline module {i} that is not a Lake root')
            elif not (i == 'Mathlib' or i.startswith('Mathlib.')):
                errors.append(f'{n} imports unknown module {i}')
        state[n] = 2

    for n in mods:
        visit(n)
    return errors + check_existing_projects()


def self_test():
    good = build()
    assert check(good) == [], check(good)
    bad = copy.deepcopy(good)
    name = next(iter(bad['modules']))
    bad['modules'][name]['sha256'] = '0' * 64
    assert any('changed module' in e for e in check(bad))
    bad = copy.deepcopy(good)
    bad['modules']['QIP.Phantom'] = {'path': 'QIP/Phantom.lean', 'sha256': '0' * 64, 'imports': []}
    assert any('module set differs' in e for e in check(bad))
    bad = copy.deepcopy(good)
    bad['baseline_lake_roots'] = bad['baseline_lake_roots'] + ['NotPublished']
    assert any('differs' in e for e in check(bad))
    print('self-test passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    path = ROOT / 'source-manifest.json'
    if args.self_test:
        self_test()
        return
    if args.check:
        errors = check(json.loads(path.read_text(encoding='utf-8')))
        for e in errors:
            print('ERROR', e)
        print('FAILED' if errors else 'Manifest verified (qip, bqp-pp and bqp-pspace sources)')
        sys.exit(1 if errors else 0)
    m = build()
    errors = check(m)
    if errors:
        for e in errors:
            print('ERROR', e)
        sys.exit('not writing an inconsistent manifest')
    path.write_text(json.dumps(m, indent=2, ensure_ascii=False) + '\n', encoding='utf-8',
                    newline='\n')
    print(f"Wrote {len(m['modules'])} modules, {len(m['baseline_modules'])} baseline imports")


if __name__ == '__main__':
    main()
