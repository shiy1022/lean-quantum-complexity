#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
: "${SLURM_JOB_ID:?Run inside a Sherlock compute allocation}"
export REV_WORKERS="${REV_WORKERS:-4}"
python3 scripts/verify.py
# lake env supplies LEAN_PATH for the pinned Mathlib checkout and its packages.
lake env bash -c '
  set -euo pipefail
  export REV_LEAN="$(command -v lean)"
  case "$("$REV_LEAN" --version)" in
    "Lean (version 4.33.1,"*) ;;
    *) echo "Expected Lean 4.33.1" >&2; exit 1 ;;
  esac
  test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "0df444a360eaa60ab8c11dca51a86af692955474"
  python3 build.py
'
python3 scripts/verify.py --build
