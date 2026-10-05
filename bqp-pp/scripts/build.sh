#!/usr/bin/env bash
set -euo pipefail
: "${SLURM_JOB_ID:?Run compilation inside a Sherlock Slurm allocation}"
cd "$(dirname "$0")/.."
export BQP_WORKERS="${BQP_WORKERS:-3}"
# Set BQP_LEAN and LEAN_PATH explicitly to use an existing pinned Mathlib cache.
# Otherwise use this project's Lake environment after fetching the Mathlib cache.
if [[ -z "${BQP_LEAN:-}" ]]; then
  export BQP_LEAN="$(lake env which lean)"
  export LEAN_PATH="$(lake env printenv LEAN_PATH)"
  export BQP_MATHLIB="$PWD/.lake/packages/mathlib"
fi
: "${LEAN_PATH:?Provide the pinned Mathlib library path}"
bqp_version="$("$BQP_LEAN" --version)"
printf '%s\n' "$bqp_version"
case "$bqp_version" in
  "Lean (version 4.33.1,"*) ;;
  *) printf 'Expected Lean 4.33.1\n' >&2; exit 1 ;;
esac
: "${BQP_MATHLIB:?Provide the pinned Mathlib checkout path for an external cache}"
bqp_revision="$(cd "$BQP_MATHLIB" && git rev-parse HEAD)"
test "$bqp_revision" = 0df444a360eaa60ab8c11dca51a86af692955474
python3 scripts/verify.py
python3 build_graph.py
python3 scripts/verify.py --build
