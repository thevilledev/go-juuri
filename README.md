# go-juuri

A persistent, path-compressed radix tree for Go, with watch channels. Writes
use copy-on-write transactions, so existing trees remain valid snapshots.
*Juuri* is Finnish for root, the meaning of the Latin *radix*.

go-juuri is the storage engine of
[go-maemmidb](https://github.com/thevilledev/go-maemmidb), available as a standalone
library with no dependencies. It matches hashicorp/go-immutable-radix's iteration
order, prefix and lower-bound seeks, and longest-prefix matching. Watches follow
the same semantics, with one documented [compatibility difference](docs/design.md#compatibility).
The [benchmarks](docs/benchmarks.md) report 2–4.6× faster operations and about a
third of the heap per key on the measured workloads.

## Install

Requires Go 1.23 or later. In your Go module, run:

```sh
go get github.com/thevilledev/go-juuri
```

To try the examples in a new directory:

```sh
mkdir juuri-example
cd juuri-example
go mod init example.com/juuri-example
go get github.com/thevilledev/go-juuri
```

Each Go example below is a complete program. Copy one into `main.go` and run
`go run .`; replace the file to try the other example.

## Read and write

Start a transaction, apply changes, and keep the tree returned by `Commit`.
Passing `nil` to `Txn` disables watch notifications for those writes.

```go
package main

import (
	"fmt"

	"github.com/thevilledev/go-juuri"
)

func main() {
	tree := juuri.New()
	txn := tree.Txn(nil)
	txn.Insert([]byte("foo"), 1)
	txn.Insert([]byte("foobar"), 2)
	tree = txn.Commit()

	fmt.Println(tree.Get([]byte("foo")))
	fmt.Println(tree.LongestPrefix([]byte("foobaz")))

	var it juuri.Iterator
	it.SeekPrefixWatch(tree, []byte("foo"))
	for value, ok := it.Next(); ok; value, ok = it.Next() {
		fmt.Println(value)
	}

	// Output:
	// 1 true
	// 1 true
	// 1
	// 2
}
```

Keys are byte slices ordered lexicographically. The tree keeps no reference to
the caller's key slices, and iterators return values only. Values have type `any`
and are not deep-copied; callers must manage changes to mutable values
themselves. `Len()` walks the tree in O(n).

## Watch for changes

`GetWatch` returns a watch for the key on a hit. On a miss, it watches the deepest
node reached by the search, so nearby changes can also trigger it. Channels are
created lazily by `Watch.Chan()`.

Commit the transaction, publish the new tree, then call `Notifier.Notify()` to
close the affected watch channels. This example runs in one goroutine; when
sharing a tree between goroutines, publish it using a mutex or an atomic value.

```go
package main

import (
	"fmt"

	"github.com/thevilledev/go-juuri"
)

func main() {
	tree := juuri.New()
	txn := tree.Txn(nil)
	txn.Insert([]byte("foo"), 1)
	tree = txn.Commit()

	watch, value, ok := tree.GetWatch([]byte("foo"))
	fmt.Println(value, ok)
	changed := watch.Chan()

	var notifier juuri.Notifier
	txn = tree.Txn(&notifier)
	txn.Insert([]byte("foo"), 2)
	tree = txn.Commit()
	notifier.Notify()

	<-changed
	fmt.Println(tree.Get([]byte("foo")))

	// Output:
	// 1 true
	// 2 true
}
```

Watch channels close once. Read and watch the newly published tree to wait for
the next change. Transactions and notifiers are not safe for concurrent use.
Call `Txn.Freeze()` before creating an iterator or watch over uncommitted writes,
or retaining `Txn.Tree()` across a write; see
[ownership and snapshots](docs/design.md#ownership-and-snapshots).

## Build tags

The default implementation uses `unsafe` in two files to store children and
short path segments within a node's allocation. Build with `-tags juuri_safe`
to select the implementation without `unsafe`. The aliases `memdb_safe` and
`purego` select the same implementation. See the [design](docs/design.md) for
the layout and allocation tradeoffs.

## Documentation

- [Design](docs/design.md): node layout, snapshots, and watch semantics.
- [Benchmarks](docs/benchmarks.md): measurements, methodology, and reproduction.
- [Development](docs/development.md): checks, fuzzing, and repository layout.

## License

[MPL-2.0](LICENSE), Copyright (c) 2026 Ville Vesilehto.
