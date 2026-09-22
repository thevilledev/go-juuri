// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

// Package juuri is a persistent (immutable, structurally shared),
// path-compressed radix tree with watch channels: the storage engine of
// go-maemmidb, as a library.
//
// A Tree is a one-word value that never changes once it comes out of a
// committed transaction, so any number of goroutines may read it without
// coordination. Writes go through a Txn, which copies the nodes it changes and
// yields a new Tree on Commit; the old one stays valid. Watchers obtain a
// channel for a key, or for every key under a prefix, that is closed when a
// committed transaction replaces what they looked at.
//
// The observable semantics -- iteration order, prefix and lower-bound seeks,
// longest-prefix matching, and the exact granularity at which watch channels
// fire -- are those of hashicorp/go-immutable-radix, so that go-memdb-style
// databases built on either behave the same.
//
// This package is the API; the tree itself lives in internal/radix and its
// lazy watch channels in internal/watch, where the design notes are. The build
// tag juuri_safe (memdb_safe and purego are honoured as well) selects the node
// layout that uses no package unsafe.
package juuri
