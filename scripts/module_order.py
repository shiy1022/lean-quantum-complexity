#!/usr/bin/env python3
"""Print the bare-name QMA proof modules in import order."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "proofs"
START = "AMPUNI-arithmetic-front"
seen = set()
active = set()
order = []

def visit(module):
    if module in seen:
        return
    if module in active:
        raise RuntimeError("local import cycle at " + module)
    source = PROOFS / (module + ".lean")
    if not source.is_file():
        raise RuntimeError("missing local import " + str(source))
    active.add(module)
    for line in source.read_text().splitlines():
        if not line.startswith("import "):
            continue
        for token in line[7:].strip().split():
            if token.startswith("«") and token.endswith("»"):
                visit(token[1:-1])
    active.remove(module)
    seen.add(module)
    order.append(module)

visit(START)
available = {p.stem for p in PROOFS.glob("*.lean")}
if available != seen:
    raise RuntimeError("source closure mismatch: extra=" + str(sorted(available - seen))[:500])
for module in order:
    print(module)
print("ordered " + str(len(order)) + " modules", file=sys.stderr)
