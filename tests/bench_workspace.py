#!/usr/bin/env python3
"""Measure workspace reuse, separating record count, byte count and NFA width."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import tempfile
import time


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--before', type=Path, required=True,
                    help='directory containing before-spark-grep and before-spark-rg')
    ap.add_argument('--after', type=Path, default=Path('bin'))
    ap.add_argument('--sources', type=Path, required=True)
    ap.add_argument('--repeats', type=int, default=5)
    args = ap.parse_args()
    if args.repeats < 1:
        ap.error('--repeats must be positive')
    programs = {tool: {'before': (args.before / ('before-' + tool)).resolve(),
                       'after': (args.after / tool).resolve()}
                for tool in ('spark-grep', 'spark-rg')}
    raw = b''.join(p.read_bytes() for p in sorted(args.sources.rglob('*'))
                   if p.is_file() and p.suffix in ('.ads', '.adb', '.ml', '.mli'))
    flat = raw.replace(b'\n', b'')
    corpora = {'tiny': b'x\n' * 400_000,
               'long-synthetic': (b'x' * 1000 + b'\n') * 13_708,
               'source': raw,
               'source-refolded': b'\n'.join(flat[i:i+1000]
                                    for i in range(0, len(flat), 1000)) + b'\n'}
    patterns = ['zzqqxx', 'a{0,50}zzqqxx', 'a{0,250}zzqqxx',
                'zzqqxxa{0,250}']
    rows = []
    with tempfile.TemporaryDirectory(prefix='spark-re-workspace-') as tmp:
        for name, data in corpora.items():
            path = Path(tmp) / name
            path.write_bytes(data)
            for pattern in patterns:
                for tool, binaries in programs.items():
                    samples = {label: [] for label in binaries}
                    expected = None
                    for trial in range(args.repeats + 1):
                        order = list(binaries)
                        if trial % 2:
                            order.reverse()
                        for label in order:
                            start = time.perf_counter()
                            result = subprocess.run(
                                [str(binaries[label]), '-hc', '-e', pattern, str(path)],
                                capture_output=True, env=dict(os.environ, LC_ALL='C'),
                                check=False)
                            elapsed = time.perf_counter() - start
                            receipt = (result.returncode, result.stdout, result.stderr)
                            if expected is None:
                                expected = receipt
                            if receipt != expected or result.returncode not in (0, 1):
                                raise RuntimeError((name, pattern, tool, label, receipt, expected))
                            if trial:
                                samples[label].append(elapsed)
                    medians = {k: statistics.median(v) for k, v in samples.items()}
                    print(f"{tool}: {name}, {pattern}: "
                          f"{medians['before'] * 1000:.2f} -> "
                          f"{medians['after'] * 1000:.2f} ms",
                          file=sys.stderr, flush=True)
                    rows.append(dict(corpus=name, pattern=pattern, tool=tool,
                                     seconds=samples, median_seconds=medians,
                                     speedup=medians['before']/medians['after']))
    print(json.dumps(dict(platform=platform.platform(), repeats=args.repeats,
        corpora={k: dict(bytes=len(v), records=v.count(b'\n'),
                        sha256=hashlib.sha256(v).hexdigest()) for k, v in corpora.items()},
        binaries={tool: {label: dict(path=str(path),
            sha256=hashlib.sha256(path.read_bytes()).hexdigest())
            for label, path in binaries.items()} for tool, binaries in programs.items()},
        cases=rows), indent=2))


if __name__ == '__main__':
    main()
