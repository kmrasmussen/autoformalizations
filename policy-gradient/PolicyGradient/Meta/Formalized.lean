/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Meta.Paper

/-!
# Formalized.lean -- what this repo means by "formalized"

A single decidable predicate, accumulated from defects. Every field is a
computation on the environment; **nothing here is discharged by judgement.**

## Why this exists rather than six independent checks

The checks began as separate rules, each added after something got through. That
worked until it didn't: the free-`logits` defect was found in `g7_smoothness`,
recorded in prose in `Goal.lean`, found again in `g1_lojasiewicz`, recorded
again -- and `mei_theorem4` kept it, until a third agent refuted it with a
two-line counterexample (`logits := 0` makes the objective constant, so ascent
never moves and the bound fails for every `c`).

The rule was known. It was written down. It did not reach the third goal,
because nothing re-judged existing goals against a newly discovered requirement.

That is what a structure buys: **adding a field re-judges everything at once.**
Not documentation -- retroactive application.

## What is deliberately NOT a field

Three requirements are real and are *not* here, because no decidable form is
known. They live in `CHECKS.md` under known-uncovered:

* **No free parameters.** Four of the ten statement defects were a quantity
  quantified the wrong way (`mei_theorem4`'s `c`, `g1`/`g2`'s `mismatch`,
  `g9`'s `astar`). "Constrained by the MDP" has no crisp definition here:
  `mismatchCoeff` qualifies because it is a definition, `0 < c` does not, and
  `logits` with a differentiability hypothesis still did not. Until the
  decidable form is found this stays outside the predicate.
* **Pinned witnesses.** Same problem.
* **"Mentions its subject."** Attempted and removed. The idea was that a goal
  tagged AKM Lemma 4.1 whose conclusion contains no derivative is not that
  lemma — which is what `g2_advantage_bound` was. Implementing it required the
  `@[paper]` attribute to carry required constants, and adding that optional
  syntax **silently emptied the goal extension**: the linter reported
  `0 goals, 0 proved, 0 open` while the build stayed green. Reverted, because a
  broken census is worse than a missing field. It is also not really decidable —
  "the conclusion mentions `fderiv`" is a proxy for "this is the paper's
  statement", and a wrong statement can mention the right constants.
* **Hypothesis consumption.** A diagnostic, not a requirement -- it gave the
  same signal for `g2_advantage_bound` (which had genuinely drifted) and
  `g2_gradient_domination` (which is the paper's statement, and simply holds
  more generally). A check reporting identically for a good and a bad case is
  not the requirement; it points at goals worth examining. It gates nothing.

Adding an escape hatch -- "a human reviewed this one" -- was considered and
rejected. A predicate defining *formalized* cannot have a field whose content is
someone's say-so; that is the thing `Goal.lean` exists to replace.
-/

namespace PolicyGradient.Meta

open Lean

/-- The machine-checkable conditions a frozen goal must satisfy.

Each field records the incident that produced it. All are decided by
`Lint.lean`; this structure is the specification those computations implement. -/
structure Formalized where
  /-- **Grounded.** The conclusion depends on a binder of the anchor type.

  Incident: the repo once reported 114 theorems and zero `sorry` while its
  headline results were about `f : ℝ → ℝ` and never mentioned an MDP. -/
  grounded : Bool
  /-- **Proved.** No `sorryAx` in the axiom set. Lean's own record, not ours. -/
  proved : Bool
  /-- **Axiom-clean.** Axioms are within `{propext, Classical.choice, Quot.sound}`.

  Incident: verified that an `axiom` declared in an agent-owned file is
  inherited by a goal importing it, with no `sorry` anywhere and the wiring
  type-checking. Only the axiom set reveals it. -/
  axiomClean : Bool
  /-- **Inhabited.** Every type the goal quantifies over admits `Nonempty`.

  A structure that cannot be built makes every goal quantifying over it vacuous
  *at once*, with no individual goal looking wrong. Conservative: instance
  search is incomplete, so a negative verdict means "not found", not "no
  inhabitant exists". -/
  inhabited : Bool
  deriving Repr, DecidableEq

/-- A goal is accepted iff every field holds. -/
def Formalized.ok (f : Formalized) : Bool :=
  f.grounded && f.proved && f.axiomClean && f.inhabited

/-- The fields that fail, for reporting. -/
def Formalized.failures (f : Formalized) : List String :=
  (if f.grounded then [] else ["grounded"])
    ++ (if f.proved then [] else ["proved"])
    ++ (if f.axiomClean then [] else ["axiomClean"])
    ++ (if f.inhabited then [] else ["inhabited"])

/-- `ok` holds exactly when nothing failed. -/
theorem Formalized.ok_iff_no_failures (f : Formalized) :
    f.ok = true ↔ f.failures = [] := by
  cases f with | mk g p a i =>
    cases g <;> cases p <;> cases a <;> cases i <;> simp [ok, failures]

end PolicyGradient.Meta
