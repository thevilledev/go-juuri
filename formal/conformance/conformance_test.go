// Copyright (c) 2026 Ville Vesilehto
// SPDX-License-Identifier: MPL-2.0

// Package conformance checks that the Lean model of the tree
// (formal/lean/JuuriFormal/Tree.lean), which the proofs are about, behaves
// exactly like the Go implementation: random scripts of writes and reads run
// through both, and every answer must agree.
//
// The model is run as an executable; build it first:
//
//	cd formal/lean && lake build conformance
//
// The test is skipped when the executable is missing. JUURI_MODEL overrides
// its path.
package conformance

import (
	"bufio"
	"bytes"
	"encoding/hex"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/thevilledev/go-juuri"
)

func modelPath(t *testing.T) string {
	t.Helper()
	p := os.Getenv("JUURI_MODEL")
	if p == "" {
		p = filepath.Join("..", "lean", ".lake", "build", "bin", "conformance")
	}
	if _, err := os.Stat(p); err != nil {
		t.Skipf("model executable %s not built (cd formal/lean && lake build conformance)", p)
	}
	return p
}

func encode(k []byte) string {
	if len(k) == 0 {
		return "-"
	}
	return hex.EncodeToString(k)
}

func show(v any, ok bool) string {
	if !ok {
		return "none"
	}
	return strconv.Itoa(v.(int))
}

func drainFwd(it *juuri.Iterator) string {
	var out []string
	for v, ok := it.Next(); ok; v, ok = it.Next() {
		out = append(out, strconv.Itoa(v.(int)))
	}
	return strings.Join(out, " ")
}

func drainRev(it *juuri.ReverseIterator) string {
	var out []string
	for v, ok := it.Previous(); ok; v, ok = it.Previous() {
		out = append(out, strconv.Itoa(v.(int)))
	}
	return strings.Join(out, " ")
}

// runGo executes a script against the Go implementation. Writes go into
// one transaction until a "C" command commits it, so that nodes written
// earlier in the same transaction are changed in place; reads see the
// transaction's state, frozen first when they hand out an iterator.
func runGo(script []string) []string {
	tree := juuri.New()
	txn := tree.Txn(nil)
	out := make([]string, 0, len(script))
	for _, line := range script {
		f := strings.Fields(line)
		var k []byte
		if len(f) > 1 && f[1] != "-" {
			k, _ = hex.DecodeString(f[1])
		}
		switch f[0] {
		case "C":
			tree = txn.Commit()
			txn = tree.Txn(nil)
			out = append(out, "ok")
		case "I":
			v, _ := strconv.Atoi(f[2])
			old, ok := txn.Insert(k, v)
			if ok {
				out = append(out, fmt.Sprintf("old %d", old.(int)))
			} else {
				out = append(out, "new")
			}
		case "D":
			old, ok := txn.Delete(k)
			if ok {
				out = append(out, fmt.Sprintf("del %d", old.(int)))
			} else {
				out = append(out, "miss")
			}
		case "P":
			out = append(out, strconv.FormatBool(txn.DeletePrefix(k)))
		case "G":
			out = append(out, show(txn.Tree().Get(k)))
		case "L":
			out = append(out, show(txn.Tree().LongestPrefix(k)))
		case "F":
			txn.Freeze()
			_, v, ok := txn.Tree().FirstPrefix(k)
			out = append(out, show(v, ok))
		case "Z":
			txn.Freeze()
			_, v, ok := txn.Tree().LastPrefix(k)
			out = append(out, show(v, ok))
		case "S":
			txn.Freeze()
			var it juuri.Iterator
			it.SeekLowerBound(txn.Tree(), k)
			out = append(out, drainFwd(&it))
		case "R":
			txn.Freeze()
			var it juuri.ReverseIterator
			it.SeekReverseLowerBound(txn.Tree(), k)
			out = append(out, drainRev(&it))
		case "X":
			txn.Freeze()
			var it juuri.Iterator
			it.SeekPrefixWatch(txn.Tree(), k)
			out = append(out, drainFwd(&it))
		case "Y":
			txn.Freeze()
			var it juuri.ReverseIterator
			it.SeekPrefixWatch(txn.Tree(), k)
			out = append(out, drainRev(&it))
		case "N":
			out = append(out, strconv.Itoa(txn.Tree().Len()))
		}
	}
	return out
}

func runModel(t *testing.T, model string, script []string) []string {
	t.Helper()
	cmd := exec.Command(model)
	cmd.Stdin = strings.NewReader(strings.Join(script, "\n") + "\n")
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	if err := cmd.Run(); err != nil {
		t.Fatalf("model: %v: %s", err, stderr.String())
	}
	var out []string
	sc := bufio.NewScanner(&stdout)
	sc.Buffer(make([]byte, 1<<20), 1<<24)
	for sc.Scan() {
		out = append(out, sc.Text())
	}
	return out
}

// script builds a random program over a small alphabet, so that keys nest,
// share prefixes and split each other's segments; one in eight keys is long
// enough to leave the compact leaf classes.
func script(r *rand.Rand, n int) []string {
	alphabet := []byte{0, 'a', 'b', 0xff}
	key := func() []byte {
		l := r.Intn(5)
		if r.Intn(8) == 0 {
			l = 30 + r.Intn(45)
		}
		k := make([]byte, l)
		for i := range k {
			k[i] = alphabet[r.Intn(len(alphabet))]
		}
		return k
	}
	var s []string
	next := 0
	for range n {
		k := encode(key())
		switch r.Intn(18) {
		case 16, 17:
			s = append(s, "C")
		case 0, 1, 2, 3, 4, 5:
			next++
			s = append(s, fmt.Sprintf("I %s %d", k, next))
		case 6, 7:
			s = append(s, "D "+k)
		case 8:
			s = append(s, "P "+k)
		case 9:
			s = append(s, "G "+k)
		case 10:
			s = append(s, "L "+k)
		case 11:
			s = append(s, "F "+k, "Z "+k)
		case 12:
			s = append(s, "S "+k)
		case 13:
			s = append(s, "R "+k)
		case 14:
			s = append(s, "X "+k, "Y "+k)
		default:
			s = append(s, "N")
		}
	}
	return s
}

func TestConformance(t *testing.T) {
	model := modelPath(t)
	seeds := 300
	if testing.Short() {
		seeds = 30
	}
	for seed := int64(1); seed <= int64(seeds); seed++ {
		r := rand.New(rand.NewSource(seed))
		s := script(r, 200)
		want := runGo(s)
		got := runModel(t, model, s)
		if len(got) != len(want) {
			t.Fatalf("seed %d: model printed %d lines, Go %d", seed, len(got), len(want))
		}
		for i := range want {
			if got[i] != want[i] {
				t.Fatalf("seed %d, command %d %q: model %q, Go %q", seed, i, s[i], got[i], want[i])
			}
		}
	}
}
