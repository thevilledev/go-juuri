# Benchmarks

[Project overview and examples](../README.md)

These measurements compare the default go-juuri build with
hashicorp/go-immutable-radix v1.3.1 and v2.1.0 on operations used by
go-memdb-style databases. The source is
[`radixdiff/bench_test.go`](../radixdiff/bench_test.go). The
[differential tests](../radixdiff/radixdiff_test.go) compare go-juuri's read results
and watch behaviour with v1.3.1 using the same random transactions, with one
documented [notification difference](design.md#compatibility).

Measured on 2026-09-22. Results describe these workloads and machines; ratios
will vary with key shape, tree size, and runtime settings.

## Setup

- 100,000 random UUID strings (36 bytes; fan-out 16), the same on every run.
  Lookups use copies of the stored keys, in a fixed random order: a lookup in
  insertion order walks the allocator's layout, not the tree.
- Every implementation stores pointers to the same row objects; values need no
  separate boxing allocation.
- Writes are untracked, which is the default of both libraries; the watch
  benchmark tracks and notifies.
- Six samples of one second per cell, `GOMAXPROCS=1`, Go 1.27.1, `GOGC=400`
  (at the default a one-second window allocates a large share of the
  collector's headroom, and whether a cycle starts inside the window is decided
  by the pacer's phase rather than by the code). Medians are reported.
- Two machines: an Apple M1 Max under ordinary desktop load, and an AMD Ryzen
  AI 9 HX PRO 370 (Zen 5, Linux 6.18) with the process pinned to one full core.

## Results

Times are per operation; ratios in parentheses are go-immutable-radix's time
divided by go-juuri's. The insert/delete row measures both commits, and the
iteration row measures a complete traversal of all 100,000 keys.

### AMD Zen 5

| Operation, 100,000 keys | go-juuri | go-immutable-radix v1 | go-immutable-radix v2 |
| --- | ---: | ---: | ---: |
| Get | 124 ns | 394 ns (3.2×) | 440 ns (3.5×) |
| LongestPrefix | 126 ns | 401 ns (3.2×) | 438 ns (3.5×) |
| Insert + commit, then delete + commit | 1.05 µs | 3.61 µs (3.4×) | 3.27 µs (3.1×) |
| Iterate all keys | 2.52 ms | 7.46 ms (3.0×) | 6.48 ms (2.6×) |
| Watch a key, update it, observe the notification | 0.95 µs | 3.48 µs (3.6×) | 3.24 µs (3.4×) |

### Apple M1 Max

| Operation, 100,000 keys | go-juuri | go-immutable-radix v1 | go-immutable-radix v2 |
| --- | ---: | ---: | ---: |
| Get | 126 ns | 376 ns (3.0×) | 578 ns (4.6×) |
| LongestPrefix | 146 ns | 398 ns (2.7×) | 581 ns (4.0×) |
| Insert + commit, then delete + commit | 1.07 µs | 3.52 µs (3.3×) | 3.16 µs (3.0×) |
| Iterate all keys | 2.27 ms | 4.68 ms (2.1×) | 4.48 ms (2.0×) |
| Watch a key, update it, observe the notification | 0.96 µs | 2.82 µs (2.9×) | 2.67 µs (2.8×) |

### Allocation and memory

Allocation counts and heap usage were the same on both machines. Collection
times are listed separately.

| Metric | go-juuri | go-immutable-radix v1 | go-immutable-radix v2 |
| --- | ---: | ---: | ---: |
| Allocations per insert + delete | 12 | 77 | 66 |
| Allocations per watch cycle | 8 | 42 | 36 |
| Allocations per full iteration | 0 | 5 | 5 |
| Heap bytes per stored key | 157 | 492 | 492 |
| Heap objects per stored key | 2.4 | 6.5 | 6.5 |
| One full collection with the tree live, Zen 5 | 15 ms | 50 ms | 45 ms |
| One full collection with the tree live, M1 Max | 14 ms | 29 ms | 27 ms |

The memory figures count the caller's key slices when the library keeps them
alive, which go-immutable-radix does and go-juuri does not. go-juuri stores path
segments without retaining the original key slices, and its iterators yield
values only.

## Reproducing

The benchmark module requires Go 1.24 or later. To use the settings from the
tables, select Go 1.27.1 and start in the repository root:

```sh
make bench > benchmarks.out
go run golang.org/x/perf/cmd/benchstat@latest -col /impl benchmarks.out
```

`make bench` runs the nested module with `GOGC=400`, `-cpu 1` (setting
`GOMAXPROCS=1`), six samples, and a one-second benchmark duration. It does not pin
the process to a core; the recorded Linux run also used CPU affinity.
`benchstat` is downloaded separately and is not a library dependency.

Avoid other builds and tests during measurement. For check and fuzz commands,
see [Development](development.md).
