# How work happens here

This repo had hidden gaps once: 114 theorems, zero `sorry`, and the headline
results were abstract statements about `f : ℝ → ℝ` that never mentioned an MDP.
See `GAPS.md`. Nothing below is bureaucracy — each rule exists because a
specific hollow proof got through.

## The separation of roles

> **Whoever finds a problem states it as a goal. Only subagents discharge goals.**

The orchestrating session is not allowed to prove things. It reads, audits,
finds defects, and writes them into `Goal.lean` as frozen `sorry` statements.
Discharging a goal is delegated to a subagent that receives the statement and
may not change it.

## File ownership

| File | Who edits it |
|---|---|
| `PolicyGradient/Goal.lean` | **the orchestrator only** (statements) |
| `PolicyGradient/Target.lean` | **the orchestrator only** (definitions) |
| `PolicyGradient/Proofs.lean` | subagents |
| everything else | either, as the task requires |

`Target.lean` is spec too, and this was a real hole for a while. `Vstar`,
`Qstar`, `mismatchCoeff` are the *vocabulary* every frozen statement is phrased
in — redefining `mismatchCoeff` to `999999` changes what `mismatch_bound` means
with no `sorry` appearing anywhere. Freezing statements while leaving their
vocabulary editable freezes nothing. The gate now rejects any branch touching
both spec and `Proofs.lean`, and prints the `Target.lean` diff for review on
SPEC changes.

Subagents may not touch `Goal.lean` or `Target.lean`. Telling a prover "don't weaken the
statement" while handing it write access is honour-system; file ownership makes
it structural.

A goal is discharged in two steps. The subagent proves a named lemma in
`Proofs.lean` with exactly the goal's type. The orchestrator then replaces the
`sorry` with a reference to it:

```lean
theorem vstar_upper ... := Proofs.vstar_upper_proof ...
```

**If the supplied lemma has the wrong type, `Goal.lean` fails to compile.** The
prover gets total freedom over *how*, and none over *what counts as done*. That
asymmetry is the whole design.

**"Goal" means literally a `sorry` theorem in `Goal.lean`** — a Lean statement
that the compiler checks and the linter counts. Not a markdown checklist, not a
TODO comment, not a line in `GAPS.md`. Prose has no teeth: it was prose that
drifted from the code and produced the seven overclaiming docstrings in the
first place.

**If a problem cannot be expressed as a statement in `Goal.lean`, stop and
discuss it.** Do not route around it with a note somewhere else. Being unable to
state it is itself the finding, and usually means one of:

* the definitions are missing (G4: transfer error and concentrability are
  undefined, so AKM §6 is not yet *representable* — that is why it has no goal);
* the objects do not exist yet, in which case state the construction goal first
  (G5 was `∃ F : VecPolicy ...`, and G1 was written against `F` before `F`
  existed);
* the problem is about process rather than mathematics, and belongs here in
  `CONTRIBUTING.md` instead.

The third case is real but rare. Reach for it last, not first.

This is not about parallelism. It is the one structural defence against the
failure this repo was built to prevent:

> **An agent must never be free to choose both what it proves and what counts
> as success.**

An agent that owns a statement and then finds it hard will weaken it — not from
bad intent, but because each small step is locally reasonable and the build goes
green. Splitting the roles takes that freedom away. The prover cannot edit the
target; the target-setter gains nothing from a weak target.

## The three routes to a hollow proof

All are the same failure — a quantity or statement the prover controls.

| Route | Looks like | Caught by |
|---|---|---|
| Weakening the conclusion | abstract `f : ℝ → ℝ` with no MDP | grounding linter |
| Adding a hypothesis | `(hloja : ...)` nobody discharges | MDP-hypothesis census |
| Degenerate witness | `Nonempty (VecPolicy ...)`, constant family | pinning conjunct |

A fourth, discovered later, is the mirror of the third:

| Free universal constant | `∀ c > 0, subopt ≤ K/c²` | goal becomes **unprovable** |

`mei_theorem4` had this: quantifying `c` universally let the caller send
`c → ∞`, asserting `Vstar - Vinf ≤ 0` everywhere. Machine-checked contradiction.
A floating quantity is a defect in *both* directions — existential and
unconstrained makes a goal too weak, universal makes it too strong.

## Rules for goals

* **Agents cannot wire.** Since only the orchestrator edits `Goal.lean`, a
  correct SOLVE branch cannot reduce `OPEN` by itself. The gate therefore
  accepts a branch that *supplies a correctly-typed lemma*; the real check is
  the wiring at merge, where a wrong type makes `Goal.lean` fail to compile.
* **Frozen.** Statements in `Goal.lean` do not change to make a proof work. If a
  goal is genuinely wrong, that is a finding: say so loudly, do not adjust it
  quietly.
* **Grounded.** A `@[paper]` claim's conclusion must depend on a `FiniteMDP`
  binder. The linter enforces this and will reject the tag otherwise. Use
  `@[infra]` for object-construction goals, `@[paper_tool]` for abstract
  machinery.
* **Pinned.** Every construction goal needs a conjunct identifying *which*
  object. `∃ F, True` is satisfied by anything.
* **Witnessed.** A goal with contradictory hypotheses is vacuously provable.
  `Witness.lean` holds a concrete MDP where the standing hypotheses demonstrably
  hold.

## Rules for proofs

* No `sorry` outside `Goal.lean`.
* No `axiom`. `#print axioms` must give exactly
  `[propext, Classical.choice, Quot.sound]`.
* Helper lemmas are encouraged; weakened statements are not.
* **"Blocked at X" is a good outcome.** An honest report of where a proof failed
  is worth more than a statement bent until it went through.

## The rule to remember

> **A hypothesis is a promise. A theorem with no callers is a promise nobody
> ever pays. Prefer a visible `sorry` to an invisible hypothesis.**

## The flow

Agents work in their own git worktree on a branch, and the orchestrator gates
the branch after they finish. The gate never runs in the agent's tree: if the
thing being checked runs the check, the check is honour-system.

```bash
# agent, at the start:
cd /tmp/autoform
git worktree add -b solve/<name> /tmp/wt-<name> main
cd /tmp/wt-<name>/policy-gradient
mkdir -p .lake/build/lib
ln -sfn ~/projects/policy-gradient-lean/.lake/packages .lake/packages
cp -r ~/projects/policy-gradient-lean/.lake/build/lib/lean .lake/build/lib/lean
lake build PolicyGradient        # ~35s once, then ~5s per edit

# agent, at the end:
rm -rf .lake/build/ir            # 37M of C IR nothing links
git add -A && git commit -m "..."

# orchestrator:
scripts/gate.sh solve/<name>     # ~9s: build, lint, compare census
```

Mathlib is symlinked, never rebuilt — no toolchain install, no download. The
warm-up copies ~9M of oleans; steady state is ~11M per worktree.

Two gotchas the gate handles and you should know about:

* `lake build` alone does **not** build `Meta.Lint` (it is only reachable
  through the exe target). The gate builds it explicitly.
* `lake env lean PaperLint.lean` on its own reads **stale oleans** and will
  report a green census over code that does not compile — verified by injecting
  a broken proof. Always build before linting.

## Checking

```
lake build                          # green, sorry only in Goal.lean
lake env lean PaperLint.lean        # grounding, reachability, goal census
```

The two numbers that matter are **OPEN frozen goals** and **MDP-level
hypotheses**. Both are computed by the build. Both should only go down.
