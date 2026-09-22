#!/bin/sh
# Copyright (c) 2026 Ville Vesilehto
# SPDX-License-Identifier: MPL-2.0
#
# Verifies that every Go source file carries the copyright line and the
# MPL-2.0 SPDX identifier in its first lines.
set -eu

cd "$(dirname "$0")/.."

fail=0
for f in $(find . -name '*.go' -not -path './.git/*' | sed 's|^\./||' | sort); do
	if ! head -n 8 "$f" | grep -q 'SPDX-License-Identifier: MPL-2.0'; then
		echo "missing SPDX header: $f"
		fail=1
	fi
	if ! head -n 8 "$f" | grep -q 'Copyright'; then
		echo "missing copyright line: $f"
		fail=1
	fi
done

[ "$fail" -eq 0 ] && echo "header check OK"
exit "$fail"
