#!/usr/bin/env bash
# A/B memory benchmark: build two git refs in release, run bench.sh against each,
# and print a side-by-side comparison. Defaults compare this branch vs main.
#
#   benchmark/gc/ab.sh [gc_ref] [base_ref]
#
# Leaves results-<label>.csv in this directory and restores the original branch.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
GC_REF="${1:-plan/copying-gc-nursery}"
BASE_REF="${2:-main}"
cd "$ROOT"

if [ -n "$(git status --porcelain)" ]; then
  echo "working tree is dirty — commit or stash first" >&2; exit 1
fi
ORIG="$(git rev-parse --abbrev-ref HEAD)"
restore() { git checkout "$ORIG" >/dev/null 2>&1 || true; }
trap restore EXIT

build_and_bench() {
  local ref="$1" label="$2"
  echo ">>> $label ($ref): building release…" >&2
  git checkout "$ref" >/dev/null 2>&1
  cargo build --release >/dev/null 2>&1
  cp target/release/gweek "$HERE/gweek-$label"
  bash "$HERE/bench.sh" "$HERE/gweek-$label" "$label" > "$HERE/results-$label.csv"
}

build_and_bench "$GC_REF" gc
build_and_bench "$BASE_REF" main
bash "$HERE/compare.sh"
