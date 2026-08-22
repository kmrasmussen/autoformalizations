# The six checks: what each is for, and what went wrong without it

Every check here exists because something got through. This file records the
incident, not just the rule — a rule without its reason gets deleted by the next
person who finds it inconvenient.

The linter (`PaperLint.lean`) runs all six. The gate (`scripts/gate.sh`) turns
the numbers into merge rules. Two numbers should only ever go down: **OPEN
frozen goals** and **MDP-level hypotheses**.

---

## The one invariant

> **An agent must never be free to choose both what it proves and what counts as
> success.**

Every check below is a way of taking one half of that freedom away. Every defect
below is a way it leaked back in.

---

## CHECK 1 — Grounding

**Rule.** A `@[paper]` claim's conclusion must depend on a `FiniteMDP` binder.

**Why.** The repo once reported *114 theorems, zero `sorry`* while its headline
results were abstract statements about `f : ℝ → ℝ` that never mentioned an MDP.
Nothing was assumed illegally; the content had simply drifted out of the
statements into hypothesis positions. Zero `sorry` measured nothing.

**Incident.** `smooth_loja_rate`, `domination_rate_abstract`, `geometric_rate` —
all proved, none about reinforcement learning.

**Trap.** The obvious implementation is wrong. Scanning the conclusion for the
constant `FiniteMDP` fails everything, because `M` appears as a local fvar, not
as the constant. The check must test fvar *dependency*.

---

## CHECK 2 — Hypothesis census (the honest debt)

**Rule.** Count and print every MDP-level hypothesis a grounded goal assumes
rather than proves.

**Why.** The cheapest way to make a hard proof go green is to assume the hard
part. It is not a cheat an agent has to plan — you need a lemma, you add it as a
hypothesis, the build passes, and each step was locally reasonable.

**Incident.** `smoothAt_V_final` assumed `hdloc`, a bound nothing proved. It
looked complete.

**Gate rule.** A SOLVE change may not increase the debt. Trading a visible
`sorry` for three invisible hypotheses shows as `OPEN 10 → 9, debt 22 → 25` and
is rejected.

---

## CHECK 3 — Goal census (`sorry` per frozen goal)

**Rule.** Every frozen goal is `[OPEN]` or `[PROVED]`. OPEN is the frontier.

**Why.** `sorry`-freedom is the wrong success metric. The right one is a pair of
numbers the build computes, both monotone decreasing. Making the frontier
*visible* is what makes it shrinkable.

**Design note.** Agents cannot wire (they may not edit `Goal.lean`), so a
correct SOLVE branch cannot reduce OPEN by itself. The gate therefore accepts a
branch that supplies a correctly-typed lemma; the real check is the wiring at
merge, where a wrong type makes `Goal.lean` fail to compile.

---

## CHECK 4 — Fidelity (unused hypotheses)

**Rule.** For every *proved* goal, report named hypotheses the proof never
consumes.

**Why.** Checks 1–3 measure a statement against its own type. This is the only
one that measures it against **what it claims to be**. A hypothesis doing no
work means either the goal is more general than claimed (retag it) or it has
drifted off the paper.

**Incident.** `g2_gradient_domination`, tagged AKM Lemma 4.1, never used `hF` —
the softmax hypothesis. After two refutations of the `‖∇V‖` form it had been
restated as a general advantage bound: true, useful, and with no gradient in it
at all. Lemma 4.1's whole content is that suboptimality is dominated by a
*gradient*. Every other signal was green.

**Traps.** Theorem bodies are reachable only via `thmInfo` (`ci.value?` is `none`
for theorems). Instance binders must be filtered by `isInternal` or they swamp
the signal. Only *proved* goals may be checked — an open goal's `_proof` sibling
can be a leftover from a superseded statement, which is exactly the false
positive that fired when `g2` was retagged.

---

## CHECK 5 — Inhabitation of quantified types

**Rule.** Every structure a frozen goal quantifies over must be `Nonempty`. The
list is **derived from the goals**, not maintained by hand.

**Why.** A theorem whose hypotheses can never hold is true and useless — "every
unicorn is friendly". Two forms:

* *Per-goal*: one goal's hypotheses clash. **Inert** — verified that such a
  theorem cannot be applied anywhere, since a caller must supply the impossible
  hypotheses. It inflates the census and nothing else.
* *Per-type*: a structure that cannot be built. Then **every goal quantifying
  over it is vacuous at once**, and no individual goal looks wrong — its binder
  just reads `(F : VecPolicy ...)`.

The second is why the obligation is per type. It also generalises: any paper
formalization has an anchor type, and the rule is *build one before proving
things about it*.

**Note on threat model.** Unlike a `sorry`, an agent cannot *choose* a vacuous
proof — it only works if the hypotheses genuinely clash, which is the
spec-writer's error, not the prover's. This check guards against a mistake, not
an attack.

**Traps.** Two implementations produced **false alarms**, which is worse than no
check: a name-convention scan for `Nonempty` theorems missed real instances, and
hand-assembling the type with `mkAppOptM` left instance arguments as unfilled
metavariables, so synthesis failed on `Policy` even though `instNonemptyPolicy`
exists. Elaborating the type from *syntax* is what works.

---

## CHECK 6 — Reachability of `@[paper_tool]`

**Rule.** Warn when supporting machinery is not transitively used by any
grounded `@[paper]` theorem.

**Why.** A theorem with no callers is a promise nobody ever pays. Three abstract
rate results have been flagged since the first run and remain unreached — they
are the original overclaiming, still visible.

---

## Still missing

* **Axiom purity is not enforced.** `#print axioms` is run by hand after each
  merge. An `axiom` declared in an agent-owned file would be inherited by a goal
  that imports it — verified working. This belongs in the linter as a per-goal
  fact, alongside the `sorry` census.
* **Paper fidelity beyond hypothesis use.** CHECK 4 catches an *unused*
  hypothesis. It cannot catch a statement that uses every hypothesis and is
  still not the paper's — wrong constant, wrong quantifier order, right shape.
  That stays human, on SPEC changes only.
