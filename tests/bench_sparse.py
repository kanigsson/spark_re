#!/usr/bin/env python3
"""Sequential before/after CLI timings for the sparse simulator refinement."""

import argparse
import hashlib
import json
import platform
import statistics
import subprocess
import time
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True, type=Path)
    parser.add_argument("--after", default=Path("bin/spark-grep"), type=Path)
    parser.add_argument("--repeats", default=5, type=int)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    executables = {"before": args.before.resolve(), "after": args.after.resolve()}
    cases = [
        ("literal miss", "needle", b"x" * 200_000 + b"\n", 1),
        ("anchored dead", "^needle", b"x" * 200_000 + b"\n", 1),
        ("nullable cycle miss", "(a?)*b", b"a" * 200_000 + b"\n", 1),
        ("late match", "needle", b"x" * 200_000 + b"needle\n", 0),
        ("wide active set", "a{0,255}b", b"a" * 20_000 + b"\n", 1),
        ("short records", "needle", b"x\n" * 20_000, 1),
    ]
    rows = []
    for name, pattern, data, expected in cases:
        samples = {label: [] for label in executables}
        # One warmup per binary, then alternate order to reduce ordering bias.
        for trial in range(args.repeats + 1):
            order = list(executables)
            if trial % 2:
                order.reverse()
            for label in order:
                start = time.perf_counter()
                result = subprocess.run(
                    [str(executables[label]), "-q", pattern],
                    input=data, capture_output=True, check=False,
                )
                elapsed = time.perf_counter() - start
                if (result.returncode, result.stdout, result.stderr) != (expected, b"", b""):
                    raise RuntimeError((name, label, result))
                if trial:
                    samples[label].append(elapsed)
        medians = {key: statistics.median(value) for key, value in samples.items()}
        rows.append({
            "case": name, "pattern": pattern, "input_bytes": len(data),
            "input_sha256": hashlib.sha256(data).hexdigest(),
            "expected_status": expected, "seconds": samples,
            "median_seconds": medians, "speedup": medians["before"] / medians["after"],
        })
    print(json.dumps({
        "platform": platform.platform(), "repeats": args.repeats,
        "binaries": {label: {"path": str(path),
                              "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                     for label, path in executables.items()},
        "cases": rows,
    }, indent=2))


if __name__ == "__main__":
    main()
