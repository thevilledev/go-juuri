# Copyright (c) 2026 Ville Vesilehto
# SPDX-License-Identifier: MPL-2.0

SHELL := /bin/sh

GOLANGCI ?= golangci-lint
GOLANGCI_VERSION ?= v2.13.2

.PHONY: all tools test race test-safe test-386 lint fmt vet headers fuzz diff check bench \
	formal formal-lean formal-conformance formal-tla

all: check

# The pinned linter, so that a local run and CI agree on the findings.
tools:
	go install github.com/golangci/golangci-lint/v2/cmd/golangci-lint@$(GOLANGCI_VERSION)

test:
	go test -count=1 ./...

race:
	go test -race -count=1 ./...

# The build without package unsafe. juuri_safe is this module's own tag;
# memdb_safe and purego are honoured too, so that a program built with either
# gets the safe engine as well.
test-safe:
	go test -tags juuri_safe -count=1 ./...
	go test -tags memdb_safe -count=1 ./...
	go test -tags purego -count=1 ./...

# 32-bit: atomic alignment, no hardware popcount.
# 32-bit build check (the tests cannot run on this host).
test-386:
	GOOS=linux GOARCH=386 go vet ./... && GOOS=linux GOARCH=386 go test -c -o /dev/null ./internal/radix
	GOOS=linux GOARCH=386 go test -c -tags juuri_safe -o /dev/null ./internal/radix

# golangci-lint, over both modules and both node layouts. The safe tags select
# the same files, so one of the three is enough here; the tests build all
# three. See .golangci.yml for the linters and why they were chosen.
lint:
	$(GOLANGCI) fmt --diff
	$(GOLANGCI) run ./...
	$(GOLANGCI) run --build-tags juuri_safe ./...
	cd radixdiff && $(GOLANGCI) run ./...

# Apply what the formatters and the auto-fixable linters suggest.
fmt:
	$(GOLANGCI) fmt
	$(GOLANGCI) run --fix ./... || true
	cd radixdiff && $(GOLANGCI) fmt && $(GOLANGCI) run --fix ./... || true

# Formatting and vet without the extra tool, for a quick local loop.
vet:
	@files=$$(gofmt -l . radixdiff); if [ -n "$$files" ]; then echo "gofmt needed:"; echo "$$files"; exit 1; fi
	go vet ./...
	cd radixdiff && go vet ./...

headers:
	sh scripts/check-headers.sh

fuzz:
	go test ./internal/radix -run '^$$' -fuzz FuzzTreeOps -fuzztime 60s
	cd radixdiff && go test . -run '^$$' -fuzz FuzzDifferential -fuzztime 60s

# The differential test against hashicorp/go-immutable-radix lives in the
# nested module radixdiff, which is the only place that depends on it.
diff:
	cd radixdiff && go test -count=1 .

check: lint headers test race test-safe diff

# The comparison with go-immutable-radix behind docs/benchmarks.md. Nothing
# else may build or test while it runs.
bench:
	cd radixdiff && GOGC=400 go test -run '^$$' -bench . -benchtime 1s -count 6 -cpu 1

# Formal verification (formal/README.md): the Lean proofs, the conformance
# test of the Lean model against this code, and the TLA+ models. Needs Lean 4
# (elan picks the pinned toolchain), and Java with tla2tools.jar for TLC.
JAVA ?= java
TLA2TOOLS ?= $(HOME)/.local/share/tlaplus/tla2tools.jar
TLC = $(JAVA) -XX:+UseParallelGC -cp $(TLA2TOOLS) tlc2.TLC -workers auto -cleanup

formal: formal-lean formal-conformance formal-tla

formal-lean:
	cd formal/lean && lake build

formal-conformance:
	cd formal/lean && lake build conformance
	cd formal/conformance && go test -count=1 .

formal-tla:
	cd formal/tla && $(TLC) -config LazyWatch.cfg LazyWatch.tla
	cd formal/tla && $(TLC) -config MCJuuriTxn.cfg MCJuuriTxn.tla
	cd formal/tla && $(TLC) -config MCJuuriTxnFork.cfg MCJuuriTxn.tla
