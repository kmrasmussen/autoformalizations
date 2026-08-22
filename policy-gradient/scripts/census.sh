#!/usr/bin/env bash
# Print the three gate numbers for the tree we are standing in: OPEN debt UNGROUNDED
# Requires a green build first -- the linter alone reads stale oleans and will
# happily report a green census over code that does not compile.
set -uo pipefail
out=$(lake env lean PaperLint.lean 2>&1)
open=$(sed -n 's/.*OPEN frozen goals[^│]*│ *\([0-9]\+\) *│.*/\1/p' <<<"$out" | head -1)
debt=$(sed -n 's/.*MDP-level hypotheses[^│]*│ *\([0-9]\+\) *│.*/\1/p' <<<"$out" | head -1)
ungr=$(sed -n 's/.*UNGROUNDED @\[paper\] claims[^│]*│ *\([0-9]\+\) *│.*/\1/p' <<<"$out" | head -1)
[[ -z "$open" || -z "$debt" || -z "$ungr" ]] && { echo "CENSUS_PARSE_FAILED" >&2; echo "$out" >&2; exit 2; }
echo "$open $debt $ungr"
