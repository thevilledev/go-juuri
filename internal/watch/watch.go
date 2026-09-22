// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

// Package watch provides the lazily materialised watch channel that the tree
// hangs on every node and every leaf.
//
// A slot stays nil until somebody actually watches it, so writers -- which
// only ever seal slots -- allocate no channels at all. A slot moves in one
// direction only: nil -> live -> sealed, or straight to sealed.
package watch

import "sync/atomic"

// cell holds a materialised watch channel.
type cell struct {
	ch chan struct{}
}

// sealedCell marks a slot whose object has been replaced by a committed
// transaction. Its channel is closed, so a reader that loses the race against
// the seal is notified immediately -- which is correct, because the object it
// looked at is stale.
var sealedCell = func() *cell {
	ch := make(chan struct{})
	close(ch)
	return &cell{ch: ch}
}()

// Slot is a lazily materialised watch channel. Its zero value is ready to use
// and costs nothing until Chan or Seal is called.
type Slot struct {
	p atomic.Pointer[cell]
}

// Chan returns the slot's watch channel, creating it on first use. The channel
// is closed when the watched object is replaced by a committed transaction.
func (s *Slot) Chan() <-chan struct{} {
	if c := s.p.Load(); c != nil {
		return c.ch
	}
	c := &cell{ch: make(chan struct{})}
	if s.p.CompareAndSwap(nil, c) {
		return c.ch
	}
	// Lost the race against another watcher or against a seal; either way
	// the winner's channel is the right one to hand out.
	return s.p.Load().ch
}

// Seal closes the slot's channel, if one was ever handed out, and makes every
// later watcher of this (now stale) object fire immediately.
func (s *Slot) Seal() {
	if old := s.p.Swap(sealedCell); old != nil && old != sealedCell {
		close(old.ch)
	}
}

// Sealed reports whether the slot has been sealed. It exists for tests and
// diagnostics.
func (s *Slot) Sealed() bool { return s.p.Load() == sealedCell }
