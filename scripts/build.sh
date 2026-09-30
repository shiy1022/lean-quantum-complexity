#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Theorems/ contains the platform's statement files. Some end in `sorry`;
# the closed QMA endpoint rebuilds their proof dependencies and audits axioms.
lake build Definitions Theorems

qma_lean="$(lake env which lean)"
qma_lean_path="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$PWD/proofs:$qma_lean_path"

while IFS= read -r qma_module; do
  printf 'CHECK %s\n' "$qma_module"
  "$qma_lean" -o "proofs/$qma_module.olean" "proofs/$qma_module.lean"
done < <(python3 scripts/module_order.py)

printf 'QMA amplification endpoint and axiom audit compiled.\n'
