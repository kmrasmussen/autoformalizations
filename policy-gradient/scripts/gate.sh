#!/usr/bin/env bash
# Local CI. Runs AFTER an agent finishes, in a persistent gate worktree the
# agent cannot touch -- never in the agent's own tree.
#
#   scripts/gate.sh <branch>
#
# Classifies the branch as SOLVE / SPEC / REJECT from its diff against main,
# rebuilds in a clean tree, and compares the census before and after.
#
# Why not gate in the agent's tree: if the thing being checked runs the check,
# the check is honour-system. An agent reporting "build green" is a claim; the
# gate re-deriving it is a fact.
set -uo pipefail

REPO="${REPO:-/tmp/autoform}"
GATE="${GATE:-/tmp/pg-gate}"
WARM="${WARM:-$HOME/projects/policy-gradient-lean}"
BASE="${BASE:-main}"
BRANCH="${1:-}"
export PATH=/nix/var/lean-work/elan/bin:$PATH

die() { echo "✗ $*" >&2; exit 1; }
[[ -n "$BRANCH" ]] || die "usage: gate.sh <branch>"
cd "$REPO" || die "no repo at $REPO"
git rev-parse --verify "$BRANCH" >/dev/null 2>&1 || die "no such branch: $BRANCH"

# ── classify ────────────────────────────────────────────────────────────────
changed=$(git diff --name-only "$BASE...$BRANCH")
[[ -n "$changed" ]] || die "branch $BRANCH changes nothing"
touches_goal=$(grep -c 'PolicyGradient/Goal\.lean$'   <<<"$changed" || true)
touches_proof=$(grep -c 'PolicyGradient/Proofs\.lean$' <<<"$changed" || true)

echo "── changed ──"; sed 's/^/  /' <<<"$changed"; echo

if   (( touches_goal && touches_proof )); then
  cat >&2 <<'MSG'
✗ REJECT: this branch edits both Goal.lean and Proofs.lean.

A change may not both alter the specification and claim to satisfy it. That is
the failure this repo exists to prevent -- see GAPS.md. Split it: one SPEC
change to the statement (reviewed on its own), one SOLVE change proving it.
MSG
  exit 1
elif (( touches_goal )); then KIND=SPEC
else                          KIND=SOLVE
fi
echo "── classified: $KIND ──"; echo

# ── gate worktree: persistent, warm, orchestrator-owned ─────────────────────
if [[ ! -d "$GATE" ]]; then
  echo "── creating gate worktree (one-time warm-up ~35s) ──"
  git worktree add --detach "$GATE" "$BASE" >/dev/null || die "worktree add failed"
  mkdir -p "$GATE/policy-gradient/.lake/build/lib"
  ln -sfn "$WARM/.lake/packages" "$GATE/policy-gradient/.lake/packages"
  cp -r "$WARM/.lake/build/lib/lean" "$GATE/policy-gradient/.lake/build/lib/lean" 2>/dev/null
fi
cd "$GATE" || die "gate worktree missing"
git checkout --detach "$BASE" -q 2>/dev/null || die "cannot check out $BASE"
git clean -qfd policy-gradient/PolicyGradient 2>/dev/null

build_and_census() {  # -> "OPEN DEBT UNGROUNDED", or exits nonzero
  cd "$GATE/policy-gradient" || return 3
  # Build FIRST. The linter alone reads stale oleans and will report a green
  # census over code that does not compile -- verified by injecting a bad proof.
  lake build PolicyGradient >/tmp/gate-build.log 2>&1 || { echo BUILD_FAILED; return 1; }
  lake build PolicyGradient.Meta.Lint >>/tmp/gate-build.log 2>&1 || { echo BUILD_FAILED; return 1; }
  ./scripts/census.sh
}

echo "── baseline ($BASE) ──"
read -r b_open b_debt b_ungr < <(build_and_census) || die "baseline build failed; see /tmp/gate-build.log"
echo "  OPEN=$b_open  debt=$b_debt  ungrounded=$b_ungr"; echo

cd "$GATE" && git merge --no-edit -q "$BRANCH" 2>/dev/null || die "merge conflict with $BASE"

echo "── candidate ($BRANCH) ──"
read -r a_open a_debt a_ungr < <(build_and_census) || {
  echo; echo "── build log (tail) ──"; tail -25 /tmp/gate-build.log
  die "candidate build FAILED"
}
echo "  OPEN=$a_open  debt=$a_debt  ungrounded=$a_ungr"; echo

# ── rules ───────────────────────────────────────────────────────────────────
fail=0
r() { if [[ $1 == ok ]]; then echo "  ✓ $2"; else echo "  ✗ $2"; fail=1; fi; }

echo "── $KIND rules ──"
[[ "$a_ungr" -eq 0 ]] && r ok "no ungrounded @[paper] claims" \
                      || r no "ungrounded @[paper] claims: $a_ungr"

if [[ $KIND == SOLVE ]]; then
  # Goal.lean must be byte-identical: enforced by diff, not by trust.
  if git diff --quiet "$BASE" HEAD -- policy-gradient/PolicyGradient/Goal.lean; then
    r ok "Goal.lean untouched"
  else
    r no "Goal.lean modified by a SOLVE change"
  fi
  [[ "$a_open" -lt "$b_open" ]] && r ok "OPEN decreased ($b_open → $a_open)" \
                                || r no "OPEN did not decrease ($b_open → $a_open) -- nothing was closed"
  # The original failure mode: swapping a visible sorry for invisible hypotheses.
  [[ "$a_debt" -le "$b_debt" ]] && r ok "debt did not grow ($b_debt → $a_debt)" \
                                || r no "debt GREW ($b_debt → $a_debt) -- a sorry was traded for hypotheses"
else
  [[ "$a_open" -ge "$b_open" ]] && r ok "no sorry disappeared ($b_open → $a_open)" \
                                || r no "OPEN dropped ($b_open → $a_open) -- a solve is hiding in a SPEC change"
  echo "  ⚠ SPEC changes need a stated justification and human approval."
  added=$(git diff "$BASE" HEAD -- policy-gradient/PolicyGradient/Goal.lean | grep -c '^+@\[' || true)
  removed=$(git diff "$BASE" HEAD -- policy-gradient/PolicyGradient/Goal.lean | grep -c '^-@\[' || true)
  echo "  ⚠ goals added: $added   goals removed: $removed"
  (( removed > 0 )) && echo "  ⚠ REMOVAL detected -- always requires explicit sign-off."
fi

rm -rf "$GATE/policy-gradient/.lake/build/ir"   # 37M of C IR we never link
echo
if (( fail )); then echo "✗ GATE FAILED ($KIND)"; exit 1; fi
echo "✓ GATE PASSED ($KIND)  OPEN $b_open → $a_open   debt $b_debt → $a_debt"
