#!/usr/bin/env python3
"""Check portable sources; optionally verify compiled objects and every selected axiom report."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((ROOT / 'source-manifest.json').read_text())
    modules = manifest['modules']
    assert manifest['lean_version'] == '4.33.1'
    assert manifest['mathlib_rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
    actual = {str(p.relative_to(ROOT / 'src')) for p in (ROOT / 'src').rglob('*.lean')}
    assert actual == {info['path'] for info in modules.values()}, 'Source closure differs from manifest'
    for name, info in modules.items():
        assert digest(ROOT / 'src' / info['path']) == info['sha256'], 'Changed source: ' + name
    active, seen = set(), set()

    def visit(name):
        if name in seen:
            return
        assert name not in active, 'Import cycle: ' + name
        active.add(name)
        for dep in modules[name]['imports']:
            if dep in modules:
                visit(dep)
        active.remove(name)
        seen.add(name)

    for target in manifest['targets']:
        visit(target)
    assert seen == set(modules), 'Modules outside target closure'
    print('Verified', len(modules), 'source hashes and dependency closure')
    if not args.build:
        return
    build = json.loads((ROOT / 'build-result.json').read_text())
    assert not build['blocked'] and set(build['modules']) == set(modules), 'Incomplete build'
    for name, info in modules.items():
        record = build['modules'][name]
        assert record['exit_code'] == 0, 'Compile failure: ' + name
        assert record['source_sha256'] == info['sha256'], 'Build source mismatch: ' + name
        assert record['olean_sha256'] == digest((ROOT / 'src' / info['path']).with_suffix('.olean')), 'Object mismatch: ' + name
    legacy = json.loads((ROOT / 'verification/legacy-audits.json').read_text())
    declarations = []
    pattern = r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for name, info in modules.items():
        source = (ROOT / 'src' / info['path']).read_text()
        expected = re.findall(r'^\s*#print\s+axioms\s+(\S+)', source, re.M)
        if name in legacy:
            array = re.search(r'for name in #\[(.*?)\] do', source, re.S)
            literals = re.findall(r'``([\w.]+)', array.group(1)) if array else []
            assert literals == legacy[name], 'Changed legacy audit: ' + name
            expected += legacy[name]
        if not expected:
            continue
        assert len(expected) == len(set(expected)), 'Duplicate requested report: ' + name
        log = (ROOT / 'logs' / (name + '.log')).read_text()
        found = {}
        rows = re.findall(pattern, log, re.M)
        if name in legacy:
            rows += re.findall(r'^\w*CHECKED\s+([^;]+); axioms\s*\[([^\]]*)\]', log, re.M)
        for declaration, axioms in rows:
            assert declaration not in found, 'Duplicate axiom report: ' + declaration
            found[declaration] = sorted(a.strip() for a in axioms.split(',') if a.strip())
            assert set(found[declaration]) <= ALLOWED, 'Forbidden axioms: ' + declaration
        assert set(expected) <= set(found), 'Missing axiom report: ' + name
        declarations.extend({'declaration': d, 'axioms': found[d], 'audit_module': name} for d in expected)
    assert any(r['declaration'] == 'ShiBQP.bqp_subset_pp' for r in declarations)
    audit = (ROOT / 'src/BQP-router-assembly-fresh-audit.lean').read_text()
    assert 'example : ShiBQP.BQP ⊆ ShiClassPP.PP := ShiBQP.bqp_subset_pp' in audit
    result = {'all_modules': len(modules), 'declaration_reports': len(declarations),
              'reused_project_modules': sum(bool(r.get('reused')) for r in build['modules'].values()),
              'job_id': build['job_id'], 'declarations': declarations}
    (ROOT / 'current-verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Verified', len(modules), 'compiled objects and', len(declarations), 'axiom reports')


if __name__ == '__main__':
    main()
