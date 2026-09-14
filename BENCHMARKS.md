# Sparse simulator measurements

The generation-stamped simulator was compared with commit `4c84e82`, using
release builds from the same GNAT Pro 27 toolchain on x86-64 Linux. Each case
runs `spark-grep -q` as a separate process, including startup, compilation and
record I/O. Results are medians of five sequential runs after one warmup per
binary; execution order alternates. Every run checks the exit status and output.

| Case | Input | Before (ms) | After (ms) | Before / after |
| --- | --- | ---: | ---: | ---: |
| Literal miss, `needle` | 200,000 `x` bytes | 51.46 | 8.28 | 6.21 |
| Anchored miss, `^needle` | 200,000 `x` bytes | 51.00 | 8.27 | 6.17 |
| Nullable cycle miss, `(a?)*b` | 200,000 `a` bytes | 53.16 | 12.86 | 4.13 |
| Late match, `needle` | 200,000 `x` bytes then `needle` | 51.18 | 8.30 | 6.17 |
| Wide active set, `a{0,255}b` | 20,000 `a` bytes | 69.65 | 97.86 | 0.71 |
| Short records, `needle` | 20,000 one-byte `x` records | 14.24 | 6.01 | 2.37 |

Each record ends in newline. Sparse and short-record searches improve in this
sample. The wide active set is about 41% slower: dense-list and stamp maintenance
can cost more than Boolean arrays when many states remain active. These are
end-to-end timings of a small synthetic corpus, not a throughput guarantee.

Workspaces are sized to the compiled state count. Initializing full-capacity
sparse workspaces instead caused a short-record regression during development;
the benchmark retains that case to make this cost visible. The local stamp,
dense and index arrays require more bytes per state than the previous Boolean
sets and worklist, so maximum-size programs still require more matching stack
space. Stack capacity is outside the proof boundary.

To reproduce, retain a release `spark-grep` from the baseline, build the current
release, and run without concurrent proof or benchmark jobs:

```sh
python3 tests/bench_sparse.py --before /path/to/baseline-spark-grep \
  --after bin/spark-grep > benchmark.json
```

The JSON includes raw samples, executable and input hashes, and platform details.
