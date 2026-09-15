# Simulator measurements

## Start-byte skipping

The start-byte filter and skip loop were compared with the committed sparse-set
baseline `355f448`, using the same release toolchain and sequential methodology
described below. Both binaries include CLI startup, compilation and record I/O.

| Case | Input | Before (ms) | After (ms) | Before / after |
| --- | --- | ---: | ---: | ---: |
| Literal miss, `needle` | 200,000 `x` bytes | 8.55 | 4.88 | 1.75 |
| Anchored dead, `^needle` | 200,000 `x` bytes | 7.93 | 5.26 | 1.51 |
| Nullable cycle miss, `(a?)*b` | 200,000 `a` bytes | 12.52 | 13.04 | 0.96 |
| Late match, `needle` | 200,000 `x` bytes then `needle` | 7.95 | 4.98 | 1.60 |
| Wide active set, `a{0,255}b` | 20,000 `a` bytes | 95.65 | 95.90 | 1.00 |
| Short records, `needle` | 20,000 one-byte `x` records | 5.75 | 4.50 | 1.28 |
| Anchored candidate bytes, `^needle` | 200,000 `n` bytes | 7.85 | 5.12 | 1.53 |
| End-only empty match, `$` | 200,000 `x` bytes | 8.17 | 5.43 | 1.50 |
| Live continuation, `a.*z` | `a`, 200,000 `x` bytes, then `z` | 12.46 | 12.63 | 0.99 |

Long misses and late matches improve by 1.5–1.8 times in this sample. The
anchored candidate-byte case confirms that interior positions can skip even
bytes which could begin a match at the first boundary. The end-only empty match
checks the benefit of scanning directly to the final boundary.

The cases with live continuations are roughly unchanged. One-byte records have
no interior bytes to skip, so their timing ratio does not establish a benefit
from skipping; it includes per-record and measurement overhead. The cached mask
and summaries add fixed storage
to each compiled program, and their construction adds work at compile time.
These measurements are not a general throughput guarantee.

## Generation-stamped sparse sets

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
