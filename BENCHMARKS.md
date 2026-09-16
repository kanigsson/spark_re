# Simulator measurements

## Workspace reuse across records

Compared with `e283872` using the same GNAT Pro 27 release toolchain on x86-64
Linux. Each invocation uses `-hc`, including startup, compilation and I/O.
Values below are **before → after, in milliseconds**, taking the median of five
sequential runs after one warmup per binary. Execution order alternates and each
run checks identical exit status, stdout and stderr. No proof or test jobs ran
during these measurements.

Corpora:

- **Tiny:** 800,000 bytes, 400,000 one-byte `x` records.
- **Long `x`:** 13,721,708 bytes, 13,708 records of 1,000 `x` bytes.
- **Sources:** 13,716,226 bytes, 389,858 records from concatenated Ada and OCaml
  sources under `~/sparkdev/spark2014/src`.
- **Refolded sources:** the same non-LF payload regrouped into 1,000-byte records;
  13,339,695 bytes and 13,327 records including the new delimiters.

| Tool | Pattern (states) | Tiny records | Long `x` records | Sources | Refolded sources |
| --- | --- | ---: | ---: | ---: | ---: |
| `spark-grep` | `zzqqxx` (7) | 24.89 → 19.63 | 23.94 → 22.23 | 46.98 → 40.84 | 26.45 → 23.79 |
| `spark-grep` | `a{0,50}zzqqxx` (107) | 555.39 → 536.38 | 42.70 → 40.70 | 1201.92 → 1197.83 | 726.21 → 728.23 |
| `spark-grep` | `a{0,250}zzqqxx` (507) | 2694.86 → 2625.06 | 116.97 → 110.94 | 5784.15 → 5707.92 | 3491.21 → 3470.29 |
| `spark-grep` | `zzqqxxa{0,250}` (507) | 62.43 → 20.13 | 24.99 → 21.98 | 84.85 → 40.35 | 26.94 → 24.13 |
| `spark-rg` | `zzqqxx` (7) | 25.17 → 20.36 | 22.14 → 23.04 | 43.75 → 39.88 | 20.62 → 23.15 |
| `spark-rg` | `a{0,50}zzqqxx` (107) | 556.03 → 535.71 | 40.72 → 42.10 | 1200.15 → 1210.13 | 721.70 → 723.90 |
| `spark-rg` | `a{0,250}zzqqxx` (507) | 2686.78 → 2631.72 | 113.82 → 111.49 | 5755.41 → 5672.62 | 3492.95 → 3477.31 |
| `spark-rg` | `zzqqxxa{0,250}` (507) | 65.43 → 20.37 | 23.61 → 24.10 | 81.27 → 40.21 | 22.97 → 23.16 |

The headline `a{0,250}zzqqxx` case improves only 2.6% in `spark-grep`, from
2.695 s to 2.625 s, or 6.74 to 6.56 microseconds per record. Its nullable prefix
activates a wide epsilon closure at each boundary. Retaining arrays removes
initialization but leaves closure construction, transition and acceptance visits.
The expected near-100-nanosecond headline was therefore not reached.

The control `zzqqxxa{0,250}` has the same 507 compiled states but a narrow entry
closure. On tiny records it improves from 62.43 to 20.13 ms (3.10×); `spark-rg`
improves from 65.43 to 20.37 ms (3.21×). The retained-workspace times are close to
the seven-state pattern, about 50 ns per record including process overhead.
On source records the same control improves from 84.85 to 40.35 ms in
`spark-grep`. This separates workspace size from active-set width and corrects
the earlier attribution of all bounded-prefix overhead to array initialization.
Long-record results include small changes in both directions; there is no
uniform throughput gain.

The 32-bit reset design retains the existing array element widths. Measured
`Matcher` storage is 224, 2,624 and 12,224 bytes at 7, 107 and 507 states,
respectively. Widening just the two stamp arrays to 64 bits would add 4,064 bytes
at 507 states, before alignment. Guarded saturation resets prove safety without
that expansion. Normal clearing costs O(1); reset work is amortized over about
2^31 generation advances per set. Initial closure can still cost O(states) per
record.

Reproduce by building `e283872` with the same toolchain and saving its binaries
as `before-spark-grep` and `before-spark-rg` in a separate directory, then run:

```sh
python3 tests/bench_workspace.py --before /path/to/before --after bin \
  --sources ~/sparkdev/spark2014/src --repeats 5 > workspace-results.json
```

The JSON includes every sample, corpus sizes and hashes, and executable hashes.
`PROOF.md` records the 3,942-check baseline (one timeout), the fully proved
4,037-check result, flow analysis, and both test modes.

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
