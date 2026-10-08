"""Check publication sources/evidence, or a new build with --build (no Lean invocation)."""
import hashlib
import json
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'manifest.json').read_text())
modules = manifest['modules']
assert set(p.name for p in (root / 'src').glob('*.lean')) == {v['path'] for v in modules.values()}
for name, info in modules.items():
    source = root / 'src' / info['path']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == info['sha256'], name
    assert re.findall(r'^import\s+(\S+)', source.read_text(), re.M) == info['imports'], name
    assert all(dep in modules or dep == 'Mathlib' or dep.startswith('Mathlib.') for dep in info['imports'])
expected = re.findall(r'``(ShiReversible[\w.]+)', (root / 'src/ReversibleAudit.lean').read_text())
assert len(expected) == len(set(expected)) == 2724
fresh = '--build' in sys.argv
result = json.loads((root / ('result.json' if fresh else 'verification/clean-build.json')).read_text())
assert set(result['modules']) == set(modules) and not result['blocked']
assert result['workers'] >= 2 and result['threads_per_process'] == 1
for name, info in modules.items():
    record = result['modules'][name]
    assert record['exit_code'] == 0 and record['source_sha256'] == info['sha256'], name
    assert re.fullmatch(r'[0-9a-f]{64}', record['olean_sha256']), name
    if fresh:
        obj = (root / 'src' / info['path']).with_suffix('.olean')
        assert hashlib.sha256(obj.read_bytes()).hexdigest() == record['olean_sha256'], name
if fresh:
    text = (root / 'logs/ReversibleAudit.log').read_text()
    checks = [dict(declaration=n, axioms=re.findall(r'[A-Za-z][\w.]*', x)) for n, x in
              re.findall(r'REVERSIBLE_CHECKED ([\w.]+); axioms \[(.*?)\]', text, re.S)]
else:
    checks = json.loads((root / 'verification/axioms.json').read_text())
assert [x['declaration'] for x in checks] == expected
for check in checks:
    assert set(check['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}, check
assert 'ShiReversibleGenerator.efficient_reversible_simulation' in expected
print(f'Verified {len(modules)} source hashes and {len(checks)} ordered unique axiom records' +
      ('; fresh object hashes verified.' if fresh else '; published object hashes are recorded evidence.'))
