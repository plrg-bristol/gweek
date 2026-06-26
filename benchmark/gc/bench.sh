#!/usr/bin/env bash
# Measure gweek peak memory + wall time per (program, strategy) and emit CSV.
#
#   benchmark/gc/bench.sh <gweek-binary> <label> > results-<label>.csv
#
# "peak memory footprint" is taken from macOS `/usr/bin/time -l` (phys_footprint
# high-water mark, in bytes) — the same metric PLAN.md uses. On Linux swap the
# parser for `/usr/bin/time -v`'s "Maximum resident set size".
set -euo pipefail

BIN="$1"
LABEL="$2"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
EX="$ROOT/examples"

# Completing programs run to full enumeration: identical solution counts on any
# branch, so peak memory is an apples-to-apples comparison.
COMPLETING="perm nqueens coins"
# Long-running program: never terminates here, bounded by a wall-clock timeout.
# This is the unbounded-garbage scenario — memory is not identical work, see README.
LONG="pythagorean"
LONG_TIMEOUT="${LONG_TIMEOUT:-12}"
REPEATS="${REPEATS:-3}"

echo "label,program,strategy,kind,repeat,real_sec,peak_bytes,peak_mb,solutions,final"

run_one() {
  local prog="$1" strat="$2" kind="$3" timeout="$4" rep="$5"
  local errf outf
  errf=$(mktemp); outf=$(mktemp)
  /usr/bin/time -l "$BIN" --"$strat" --timeout "$timeout" "$EX/$prog.gwk" >"$outf" 2>"$errf" || true
  local peak real sols final peak_mb
  peak=$(awk '/peak memory footprint/{print $1}' "$errf")
  real=$(awk '/ real /{print $1}' "$errf")
  sols=$(grep -c '^>' "$outf" || true)
  final=$(grep '>>>' "$outf" | tail -1 | tr -d ',')
  peak_mb=$(awk -v b="$peak" 'BEGIN{printf "%.1f", b/1048576}')
  echo "$LABEL,$prog,$strat,$kind,$rep,$real,$peak,$peak_mb,$sols,$final"
  rm -f "$errf" "$outf"
}

for prog in $COMPLETING; do
  for strat in bfs fair dfs; do
    for r in $(seq 1 "$REPEATS"); do run_one "$prog" "$strat" complete 60 "$r"; done
  done
done
for prog in $LONG; do
  for strat in bfs fair dfs; do run_one "$prog" "$strat" long "$LONG_TIMEOUT" 1; done
done
