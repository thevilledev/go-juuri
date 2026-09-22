# Development

[Project overview and examples](../README.md)

Run the commands below from the repository root. The library requires Go 1.23
or later; the differential tests and benchmarks in the nested `radixdiff`
module require Go 1.24 or later. Running the full checks therefore requires
Go 1.24 or later, plus `make`, a C toolchain for the race detector, and
golangci-lint:

```sh
make tools
```

That installs the pinned golangci-lint into `$(go env GOPATH)/bin`; set
`GOLANGCI` to use a copy from somewhere else.

## Checks

```sh
make check
```

This lints both modules, checks license headers, and runs the library tests,
race detector, all three safe-build tags, and differential tests.

Individual targets are available for focused checks:

| Command | Check |
| --- | --- |
| `make test` | Library tests |
| `make race` | Library tests with the race detector |
| `make test-safe` | Tests with `juuri_safe`, `memdb_safe`, and `purego` |
| `make test-386` | Linux/386 vet and compilation checks; does not run tests |
| `make lint` | golangci-lint over both modules and both node layouts |
| `make vet` | Formatting and `go vet` only, with no extra tool installed |
| `make headers` | Copyright and MPL-2.0 headers in Go source files |
| `make diff` | Differential tests against go-immutable-radix v1 |

`make lint` reports problems without changing files. To apply the formatting
and the fixes the linters can make themselves:

```sh
make fmt
```

The enabled linters, and the reasoning behind the selection, are in
[`.golangci.yml`](../.golangci.yml). The default node layout is linted, then
the `juuri_safe` one, because the two builds share no node declaration.

## Fuzzing

```sh
make fuzz
```

This runs `FuzzTreeOps` against a reference model for 60 seconds, then
`FuzzDifferential` against go-immutable-radix v1 for 60 seconds. Both check reads,
writes, iteration, and watch behaviour. The model fuzzer also retains iterators
over uncommitted state across later writes.

## Benchmarks

```sh
make bench
```

Run benchmarks separately from other builds and tests. See
[Benchmarks](benchmarks.md#reproducing) for the measurement settings and commands
to capture and summarise results.

## Repository layout

The root package is the public API and holds no logic: each of its methods
forwards to `internal/radix`, which is where the tree lives. Only the wiring is
tested at the root ([`api_test.go`](../api_test.go),
[`example_test.go`](../example_test.go)); the tree's own tests sit next to it in
`internal/radix`.

| Path | Purpose |
| --- | --- |
| [`tree.go`](../tree.go), [`txn.go`](../txn.go), [`iter.go`](../iter.go) | The exported API, over the internal tree |
| [`internal/radix/tree.go`](../internal/radix/tree.go) | Immutable trees and lookups |
| [`internal/radix/txn.go`](../internal/radix/txn.go) | Write transactions, ownership epochs, and notifications |
| [`internal/radix/iter.go`](../internal/radix/iter.go) | Forward and reverse iteration |
| [`internal/radix/node.go`](../internal/radix/node.go) | Shared node operations |
| `internal/radix/node_{unsafe,safe}.go`, `segment_{unsafe,safe}.go` | Node layout and path storage for each build |
| [`internal/watch/`](../internal/watch/) | Lazily materialised watch channels |
| [`radixdiff/`](../radixdiff/) | Differential tests and comparison benchmarks |
| [`docs/`](./) | Supporting documentation |

The nested module keeps go-immutable-radix out of the library's dependencies.
Its differential tests apply the same random transactions to go-juuri and
go-immutable-radix v1, then compare read results and watch notifications. See
[Compatibility](design.md#compatibility) for the known notification difference.
Benchmarks compare go-juuri with both v1 and v2. Root-level `go test ./...` does
not include this module; use `make diff` or `make check` to test it.

The [CI workflow](../.github/workflows/ci.yml) also exercises supported Go
versions on Linux and macOS, runs Linux/386 tests, fuzzes briefly, and runs
each benchmark once as a correctness check.
