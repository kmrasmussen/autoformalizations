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
# Goal.lean AND Target.lean are both spec. A definition is vocabulary every
# statement is phrased in: weakening `mismatchCoeff` changes what
# `mismatch_bound` MEANS, with no sorry appearing anywhere.
touches_spec=$(grep -cE 'PolicyGradient/(Goal|Target)\.lean$' <<<"$changed" || true)
touches_proof=$(grep -c 'PolicyGradient/Proofs\.lean$' <<<"$changed" || true)

echo "── changed ──"; sed 's/^/  /' <<<"$changed"; echo

if   (( touches_spec && touches_proof )); then
  cat >&2 <<'MSG'
✗ REJECT: this branch edits both the spec (Goal.lean / Target.lean) and Proofs.lean.

A change may not both alter the specification and claim to satisfy it. That is
the failure this repo exists to prevent -- see GAPS.md. Split it: one SPEC
change (reviewed on its own), one SOLVE change proving it.

Target.lean counts as spec: `Vstar`, `Qstar`, `mismatchCoeff` are the
vocabulary every frozen statement is phrased in. Redefining one changes what
the goals mean without any sorry appearing.
MSG
  exit 1
elif (( touches_spec )); then KIND=SPEC
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
base_out=$(build_and_census); base_rc=$?
[[ $base_rc -eq 0 && "$base_out" != *BUILD_FAILED* ]] \
  || { tail -25 /tmp/gate-build.log; die "baseline build failed"; }
read -r b_open b_debt b_ungr <<<"$base_out"
echo "  OPEN=$b_open  debt=$b_debt  ungrounded=$b_ungr"; echo

cd "$GATE" && git merge --no-edit -q "$BRANCH" 2>/dev/null || die "merge conflict with $BASE"

echo "── candidate ($BRANCH) ──"
cand_out=$(build_and_census); cand_rc=$?
if [[ $cand_rc -ne 0 || "$cand_out" == *BUILD_FAILED* ]]; then
  echo "  ✗ BUILD FAILED"; echo
  echo "── build log (tail) ──"; grep -E "^error|error:" /tmp/gate-build.log | head -12
  echo; echo "✗ GATE FAILED ($KIND): candidate does not compile"
  rm -rf "$GATE/policy-gradient/.lake/build/ir"
  exit 1
fi
read -r a_open a_debt a_ungr <<<"$cand_out"
echo "  OPEN=$a_open  debt=$a_debt  ungrounded=$a_ungr"; echo

# ── rules ───────────────────────────────────────────────────────────────────
fail=0
r() { if [[ $1 == ok ]]; then echo "  ✓ $2"; else echo "  ✗ $2"; fail=1; fi; }

echo "── $KIND rules ──"
[[ "$a_ungr" -eq 0 ]] && r ok "no ungrounded @[paper] claims" \
                      || r no "ungrounded @[paper] claims: $a_ungr"

if [[ $KIND == SOLVE ]]; then
  # Goal.lean must be byte-identical: enforced by diff, not by trust.
  if git diff --quiet "$BASE" HEAD -- policy-gradient/PolicyGradient/Goal.lean \
                                      policy-gradient/PolicyGradient/Target.lean; then
    r ok "spec untouched (Goal.lean, Target.lean)"
  else
    r no "spec modified by a SOLVE change"
  fi
  # An agent may not edit Goal.lean, so OPEN cannot drop inside its branch.
  # What we require instead: at least one new lemma in Proofs.lean. The typed
  # wiring is the real check and happens at merge -- a wrong-typed lemma makes
  # Goal.lean fail to compile there.
  newlemmas=$(git diff "$BASE" HEAD -- policy-gradient/PolicyGradient/Proofs.lean \
              | grep -cE '^\+\s*(theorem|lemma) ' || true)
  if [[ "$a_open" -lt "$b_open" ]]; then
    r ok "OPEN decreased ($b_open → $a_open)"
  elif (( newlemmas > 0 )); then
    r ok "supplies $newlemmas new lemma(s) for wiring (OPEN unchanged: agents cannot wire)"
  else
    r no "no new lemmas and OPEN unchanged -- this branch closes nothing"
  fi
  # The original failure mode: swapping a visible sorry for invisible hypotheses.
  [[ "$a_debt" -le "$b_debt" ]] && r ok "debt did not grow ($b_debt → $a_debt)" \
                                || r no "debt GREW ($b_debt → $a_debt) -- a sorry was traded for hypotheses"
else
  [[ "$a_open" -ge "$b_open" ]] && r ok "no sorry disappeared ($b_open → $a_open)" \
                                || r no "OPEN dropped ($b_open → $a_open) -- a solve is hiding in a SPEC change"
  echo "  ⚠ SPEC changes need a stated justification and human approval."
  added=$(git diff "$BASE" HEAD -- policy-gradient/PolicyGradient/Goal.lean | grep -c '^+@\[' || true)
  removed=$(git diff "$BASE" HEAD -- policy-gradient/PolicyGradient/Goal.lean | grep -c '^-@\[' || true)
  # Any change to Target.lean matters, not just `def` lines: a definition BODY
  # is where the meaning lives (`mismatchCoeff := 999999` touches no `def` line).
  defs=$(git diff "$BASE" HEAD -- policy-gradient/PolicyGradient/Target.lean \
         | grep -cE '^[+-][^+-]' || true)
  if (( defs > 0 )); then
    echo "  ⚠ Target.lean CHANGED ($defs lines) -- definitions are the vocabulary every"
    echo "    frozen statement is phrased in. Changing one silently changes what the"
    echo "    goals MEAN, with no sorry appearing anywhere. Review against the paper."
    git diff "$BASE" HEAD -- policy-gradient/PolicyGradient/Target.lean \
      | grep -E '^[+-][^+-]' | head -20 | sed 's/^/      /'
  fi
  echo "  ⚠ goals added: $added   goals removed: $removed"
  (( removed > 0 )) && echo "  ⚠ REMOVAL detected -- always requires explicit sign-off."
fi

rm -rf "$GATE/policy-gradient/.lake/build/ir"   # 37M of C IR we never link
echo
if (( fail )); then echo "✗ GATE FAILED ($KIND)"; exit 1; fi
echo "✓ GATE PASSED ($KIND)  OPEN $b_open → $a_open   debt $b_debt → $a_debt"
