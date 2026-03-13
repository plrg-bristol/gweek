#!/usr/bin/env python3
"""Benchmark Gweek vs KiCS2 and PAKCS (Curry).

Runs each benchmark multiple times and reports median wall-clock time.

Usage:
    python3 benchmark/run.py [--pakcs] [--kics2] [--runs N]

Configuration (environment variables):
    GWEEK_BIN    Path to gweek binary        (default: target/release/gweek)
    PAKCS_BIN    Path to pakcs binary         (default: benchmark/pakcs-3.8.0/bin/pakcs)
    KICS2_DIR    Path to KiCS2 install root   (default: benchmark/kics2-3.3.0-arm64-darwin)
"""

import argparse
import os
import platform
import statistics
import subprocess
import sys
import time

# ── Paths ────────────────────────────────────────

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT_DIR = os.path.dirname(SCRIPT_DIR)

GWEEK = os.environ.get("GWEEK_BIN", os.path.join(ROOT_DIR, "target", "release", "gweek"))
PAKCS = os.environ.get("PAKCS_BIN", os.path.join(SCRIPT_DIR, "pakcs-3.8.0", "bin", "pakcs"))
KICS2_DIR = os.environ.get("KICS2_DIR", os.path.join(SCRIPT_DIR, "kics2-3.3.0-arm64-darwin"))
KICS2I = os.path.join(KICS2_DIR, "bin", ".local", "kics2i")

CURRY_DIR = os.path.join(SCRIPT_DIR, "curry")
GWEEK_DIR = os.path.join(ROOT_DIR, "examples")
GWEEK_BENCH = os.path.join(SCRIPT_DIR, "gweek")

TIMEOUT = 300

# ── Benchmarks ───────────────────────────────────

BENCHMARKS = [
    # (name, solutions, gweek_file, curry_file, pakcs_ok, kics2_ok)
    ("perm(7)",        5040,  f"{GWEEK_BENCH}/perm_simple.gwk", f"{CURRY_DIR}/PermSimple.curry", True,  True),
    ("nqueens(8)",     92,    f"{GWEEK_DIR}/nqueens.gwk",       f"{CURRY_DIR}/NQueens.curry",    True,  True),
    ("coins(20)",      11691, f"{GWEEK_DIR}/coins.gwk",         f"{CURRY_DIR}/Coins.curry",      True,  True),
    ("permsort(12)",   1,     f"{GWEEK_BENCH}/permsort.gwk",    f"{CURRY_DIR}/PermSort.curry",   True,  True),
    ("half(1600)",     1,     f"{GWEEK_BENCH}/half.gwk",        f"{CURRY_DIR}/Half.curry",       True,  True),
    ("last(100)",      1,     f"{GWEEK_BENCH}/last.gwk",        f"{CURRY_DIR}/Last.curry",       True,  True),
    ("find_list(7,5)", 462,   f"{GWEEK_DIR}/find_list.gwk",     f"{CURRY_DIR}/FindList.curry",   False, True),
]

# ── Timing ───────────────────────────────────────

def time_cmd(args, runs, env=None):
    """Run a command `runs` times, return median wall-clock seconds."""
    times = []
    for _ in range(runs):
        start = time.perf_counter()
        subprocess.run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
        elapsed = time.perf_counter() - start
        times.append(elapsed)
    return statistics.median(times)


def time_gweek(file, flags, runs):
    return time_cmd([GWEEK] + flags + ["--timeout", str(TIMEOUT), file], runs)


def time_pakcs(file, runs):
    return time_cmd([PAKCS, "--nocypm", ":load", file, ":eval", "count", ":quit"], runs)


def time_kics2(file, runs):
    env = {**os.environ, "KICS2HOME": KICS2_DIR, "CURRYPATH": os.path.join(KICS2_DIR, "lib")}
    return time_cmd([KICS2I, "--nocypm", ":load", file, ":eval", "count", ":quit"], runs, env=env)


def speedup(other, gweek):
    if other is None:
        return "—"
    return f"{other / gweek:.0f}×"


def fmt_time(t):
    if t is None:
        return "DNF"
    return f"{t:.3f}s"

# ── Main ─────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--pakcs", action="store_true", help="Also benchmark PAKCS (slow)")
    parser.add_argument("--kics2", action="store_true", default=None, help="Also benchmark KiCS2 (default: auto-detect)")
    parser.add_argument("--runs", type=int, default=3, help="Runs per benchmark (default: 3)")
    args = parser.parse_args()

    runs = args.runs
    use_pakcs = args.pakcs
    use_kics2 = args.kics2 if args.kics2 is not None else os.path.isfile(KICS2I) and os.access(KICS2I, os.X_OK)

    # Validate
    if not os.access(GWEEK, os.X_OK):
        print(f"Error: gweek not found at {GWEEK}", file=sys.stderr)
        print("  Build with: cargo build --release", file=sys.stderr)
        print("  Or set GWEEK_BIN=/path/to/gweek", file=sys.stderr)
        sys.exit(1)
    if use_pakcs and not os.access(PAKCS, os.X_OK):
        print(f"Error: PAKCS not found at {PAKCS}", file=sys.stderr)
        print("  Set PAKCS_BIN=/path/to/pakcs or omit --pakcs", file=sys.stderr)
        sys.exit(1)
    if use_kics2 and not os.access(KICS2I, os.X_OK):
        print(f"Error: KiCS2 not found at {KICS2I}", file=sys.stderr)
        print("  Set KICS2_DIR=/path/to/kics2 or omit --kics2", file=sys.stderr)
        sys.exit(1)

    # Warm up KiCS2 (first run compiles Curry → Haskell → native)
    if use_kics2:
        print("Warming up KiCS2...", file=sys.stderr)
        for name, _, _, curry_file, _, kics2_ok in BENCHMARKS:
            if kics2_ok:
                time_kics2(curry_file, 1)
        print(file=sys.stderr)

    # Header
    competitors = ""
    if use_kics2:
        competitors += " vs KiCS2"
    if use_pakcs:
        competitors += " vs PAKCS"

    print(f"Benchmark: Gweek{competitors}")
    print("=" * 40)
    uname = platform.machine()
    try:
        cpu = subprocess.check_output(["sysctl", "-n", "machdep.cpu.brand_string"], stderr=subprocess.DEVNULL).decode().strip()
    except Exception:
        cpu = "unknown"
    print(f"System: {uname}, {cpu}")
    print(f"Gweek:  release build ({GWEEK})")
    if use_kics2:
        print(f"KiCS2:  ({KICS2_DIR})")
    if use_pakcs:
        print(f"PAKCS:  ({PAKCS})")
    print(f"Runs:   {runs} (median wall-clock time)")
    print()

    # Build column spec
    columns = [
        ("Benchmark",  "16"),
        ("Solns",       "6"),
        ("BFS",         "8"),
        ("DFS",         "8"),
        ("Fair",        "8"),
        ("BFS -o",      "8"),
        ("DFS -o",      "8"),
    ]
    if use_kics2:
        columns += [("KiCS2", "8"), ("vs K", "7")]
    if use_pakcs:
        columns += [("PAKCS", "8"), ("vs P", "7")]

    def print_row(values):
        parts = []
        for (_, width), val in zip(columns, values):
            parts.append(f"{val:>{width}}")
        print("  ".join(parts))

    # Header row
    print_row([name for name, _ in columns])
    print_row(["—" * int(w) for _, w in columns])

    # Run benchmarks
    for name, solns, gweek_file, curry_file, pakcs_ok, kics2_ok in BENCHMARKS:
        print(f"  Running {name}...", end="", flush=True, file=sys.stderr)

        gb  = time_gweek(gweek_file, ["--bfs"], runs)
        gd  = time_gweek(gweek_file, ["--dfs"], runs)
        gf  = time_gweek(gweek_file, ["--fair"], runs)
        gbo = time_gweek(gweek_file, ["--bfs", "-o"], runs)
        gdo = time_gweek(gweek_file, ["--dfs", "-o"], runs)

        row = [f"{name:<16}", str(solns), fmt_time(gb), fmt_time(gd), fmt_time(gf), fmt_time(gbo), fmt_time(gdo)]

        if use_kics2:
            k = time_kics2(curry_file, runs) if kics2_ok else None
            row += [fmt_time(k), speedup(k, gd)]

        if use_pakcs:
            p = time_pakcs(curry_file, runs) if pakcs_ok else None
            row += [fmt_time(p), speedup(p, gd)]

        print_row(row)
        print(" done", file=sys.stderr)

    print()
    print("Speedups are Gweek DFS vs competitor (both use DFS).")
    print("DNF = did not finish (>5 min).")


if __name__ == "__main__":
    main()
