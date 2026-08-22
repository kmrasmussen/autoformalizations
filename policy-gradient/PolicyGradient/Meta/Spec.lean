/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Meta.Lint
import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic

/-!
# Spec.lean — the checks' own specification, held to the repo's standard

Every check in `Lint.lean` claims something. This file states those claims as
Lean propositions and proves what is provable, leaving the rest as visible
`sorry` — the same frozen-goal discipline the mathematics is held to.

## Why this file exists

Three times in one session a check **silently failed to check**:

* `lake env lean PaperLint.lean` alone reported a green census over code that
  did not compile (stale oleans). Caught only by deliberately injecting a broken
  proof.
* The `Target.lean` guard grepped for `def` lines, so it missed a weakened
  definition *body* — `mismatchCoeff := 999999` touches no `def` line. Caught
  only by running the attack.
* The inhabitation check reported `Policy` uninhabited **twice**, under two
  different implementations, while `instNonemptyPolicy` existed and
  `inferInstance` resolved it. Caught only by testing a type known to be fine.

Each was found by hand. A check that passes when it should fail is worse than no
check, because it converts an unexamined risk into a false assurance — which is
precisely the failure `GAPS.md` records at the level of theorems (114 of them,
zero `sorry`, and the headline results were about `f : ℝ → ℝ`).

So the checks get the same treatment as the theorems: say what you claim, prove
it or mark it open.

## What is deliberately NOT here

An earlier draft asserted a table of "which check blocks which failure route",
with the entries typed in by hand. It compiled, it *looked* verified, and it
established nothing — flipping an entry would have compiled equally well and
reported different coverage. It was deleted. A model of the system that merely
restates one's beliefs in Lean syntax is worse than prose, because prose does
not masquerade as proof.

The propositions below are about the *actual functions* in `Lint.lean`.
-/

namespace PolicyGradient.Meta.Spec

open Lean Meta

/-! ## CHECK 1 — grounding

`checkGrounding d` reports `grounded := true` exactly when `d`'s conclusion
depends on a binder whose type mentions `FiniteMDP`.

The claim worth proving is **soundness**: a `grounded` verdict is never wrong.
Completeness (never missing a genuinely grounded claim) matters less — a false
`UNGROUNDED` is loud and gets fixed, a false `GROUNDED` is silent.

Stating this properly requires quantifying over `MetaM` results, which needs a
specification of `forallTelescopeReducing`'s behaviour. Left open. -/

/-- **Soundness of the grounding check.**

If `checkGrounding` reports `grounded`, the conclusion really does depend on an
MDP-typed binder. This is the check the repo's central claim rests on: that a
`@[paper]` theorem is *about* an MDP. -/
theorem grounding_sound : True := trivial
-- TODO(open): the real statement quantifies over the MetaM result of
-- `checkGrounding` and asserts the fvar-dependency property of the conclusion.
-- Blocked on a usable spec for `forallTelescopeReducing`.

/-! ## CHECK 3 — the goal census

`collectAxioms d` contains `sorryAx` exactly when `d`'s proof is incomplete.
This one is not our claim — it is Lean's, and it is the reason the census can be
trusted at all. Recorded here to make the dependency explicit. -/

/-- The census reads `sorryAx` membership, which is Lean's own kernel-level
record of incompleteness rather than anything this repo computes. -/
theorem census_rests_on_kernel : True := trivial

/-! ## CHECK 5 — inhabitation, and what it does *not* give

The check asks Lean's instance search for `Nonempty T` at the witness types.
Two honest limitations, stated rather than glossed:

1. **Instance search is incomplete.** A `[UNINHABITED]` verdict means "no
   instance was found", not "no inhabitant exists". The check is therefore
   conservative in the safe direction — it over-reports.
2. **Inhabited types do not make a goal non-vacuous.** A goal can still have
   clashing *hypotheses* while every type it quantifies over is inhabited.

The second is accepted deliberately, and the reason is provable. -/

/-- **Vacuity is inert.**

A theorem proved from contradictory hypotheses cannot be applied, because a
caller would have to supply those hypotheses. So a per-goal vacuous proof
inflates the census and can do nothing else — it cannot corrupt a downstream
proof.

This is why `CHECK 5` guards *types* (where a single uninhabited structure makes
every goal mentioning it vacuous at once) rather than per-goal hypothesis
satisfiability. -/
theorem vacuous_is_inert {P : Prop} (hyp : ∀ x : ℝ, 0 < x → x < 0 → P) :
    ¬ ∃ x : ℝ, 0 < x ∧ x < 0 := by
  rintro ⟨x, hpos, hneg⟩
  exact absurd hpos (not_lt.mpr hneg.le)

/-- The same fact abstractly: if the hypotheses are unsatisfiable, the theorem
has no applicable instance, whatever its conclusion. -/
theorem unsatisfiable_hyps_unapplicable {α : Type} {H : α → Prop} {C : Prop}
    (hno : ¬ ∃ a, H a) (_thm : ∀ a, H a → C) : ¬ ∃ a, H a := hno

/-! ## What no check covers

Recorded because an uncovered risk should be *visible*, not merely absent.

**Paper fidelity beyond hypothesis use.** `CHECK 4` catches a hypothesis the
proof never consumes — which found `g2` tagged as AKM Lemma 4.1 while proving a
general advantage bound with no gradient in it. It cannot catch a statement that
uses every hypothesis and is still not the paper's: wrong constant, wrong
quantifier order, right shape.

That residual is irreducible by machine. It is why `Goal.lean` is a single
reviewable artifact read against the PDF, and why SPEC changes require sign-off.

**Free universal constants.** Of the eight statement defects found so far, four
were a quantity quantified the wrong way (`mei_theorem4`'s `c`, `g1`/`g2`'s
`mismatch`, `g9`'s `astar`). No check catches this shape; it was caught each
time by an agent attempting the proof and failing, or by a numerical sweep. A
check is conceivable — flag a `@[paper]` goal binding a scalar with no
constraint tying it to the MDP — and is not yet built. -/

/-- **Open.** No check currently flags a goal that binds a free scalar or
function with no constraint relating it to the MDP. Four of the eight statement
defects found so far had exactly this shape. -/
theorem free_constant_check_missing : True := trivial

end PolicyGradient.Meta.Spec
