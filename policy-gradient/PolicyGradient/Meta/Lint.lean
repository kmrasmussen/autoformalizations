/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Meta.Paper
import PolicyGradient.Meta.Formalized

/-!
# The paper-claim linter

Three checks over every `@[paper]` / `@[paper_tool]` annotation in the
environment.

## Check 1 — grounding

A `@[paper]` claim asserts *this declaration is that paper result*. Papers about
policy gradient are about Markov decision processes, so the claim is only honest
if the theorem's **conclusion** actually says something about a `FiniteMDP`.

The check walks the binder telescope, records the `FVarId`s of binders whose
type mentions `PolicyGradient.FiniteMDP`, and asks whether the conclusion has an
fvar dependency on any of them.

Note the subtlety: it is *not* enough to scan the conclusion for the constant
`FiniteMDP`. In a statement like

    theorem foo (M : FiniteMDP S A) (s : S) : V M π m s = ...

the conclusion mentions `M`, a local **free variable** — the constant
`FiniteMDP` occurs only in `M`'s *type*, never in the conclusion itself. A
syntactic `Expr.find?` for the constant therefore reports every real theorem as
ungrounded. The dependency test is the correct one.

Ungrounded `@[paper]` claims fail the build.

For grounded claims the linter also prints every **hypothesis** (a `Prop`-typed
binder) that itself depends on an MDP binder. Those are the assumptions the
theorem takes about the MDP rather than proves — the declared gaps.

## Check 2 — reachability

A `@[paper_tool]` claims to be *machinery for* a paper result. Machinery nothing
uses is not machinery. The check computes the transitive use-set of the
`@[paper]`-grounded theorems and reports any tool outside it. Currently a
warning, not an error.

## Check 3 — summary

Totals, plus the count of MDP-level hypotheses across grounded claims. That
number is the repo's honest debt; it should only go down.
-/

open Lean Meta Elab PolicyGradient.Meta

namespace PolicyGradient.Meta

/-- The constant a `@[paper]` conclusion must depend on for the claim to be
about an actual Markov decision process. -/
def mdpConst : Name := `PolicyGradient.FiniteMDP

/-- Does this expression mention `PolicyGradient.FiniteMDP` as a constant? -/
def mentionsMDP (e : Expr) : Bool :=
  (e.find? (·.isConstOf mdpConst)).isSome

/-- The outcome of grounding-checking one `@[paper]` claim. -/
structure Grounding where
  /-- Does the conclusion depend on an MDP-typed binder? -/
  grounded : Bool
  /-- Pretty-printed hypotheses that themselves mention an MDP binder. -/
  mdpHyps : Array String
  /-- The pretty-printed conclusion, for diagnostics. -/
  concl : String

/-- Check whether `declName`'s conclusion is grounded in a `FiniteMDP` binder,
and collect the MDP-level hypotheses.

Walks the telescope; a binder is an *MDP binder* if its type mentions the
constant `FiniteMDP`. The conclusion is grounded iff it has an fvar dependency
on one of those binders — see the module docstring for why the syntactic scan is
wrong. -/
def checkGrounding (declName : Name) : MetaM Grounding := do
  let some ci := (← getEnv).find? declName
    | throwError "paper linter: unknown declaration {declName}"
  -- Pretty-print with notation and without pedantic qualification, so the
  -- hypotheses read the way they do in the source file.
  withOptions (fun o => (o.setBool `pp.notation true).setBool `pp.fullNames false) do
  forallTelescopeReducing ci.type fun binders body => do
    -- Binders whose *type* mentions FiniteMDP: the MDP itself, and anything
    -- indexed by it.
    let mut mdpFvars : Array FVarId := #[]
    for b in binders do
      let ty ← inferType b
      if mentionsMDP ty then
        mdpFvars := mdpFvars.push b.fvarId!
    -- Grounded iff the conclusion actually *uses* one of them.
    let grounded := body.hasAnyFVar (fun f => mdpFvars.contains f)
    -- Hypotheses (Prop binders) that themselves talk about the MDP.
    let mut hyps : Array String := #[]
    if grounded then
      for b in binders do
        let ty ← inferType b
        if (← isProp ty) then
          -- an MDP-level hypothesis mentions an MDP binder (or FiniteMDP itself)
          if ty.hasAnyFVar (fun f => mdpFvars.contains f) || mentionsMDP ty then
            let nm ← b.fvarId!.getUserName
            hyps := hyps.push s!"{nm} : {← ppExpr ty}"
    return { grounded, mdpHyps := hyps, concl := toString (← ppExpr body) }

/-- Constants in the `PolicyGradient` namespace that `declName`'s *proof term*
directly uses. -/
def directUses (env : Environment) (declName : Name) : Array Name := Id.run do
  let some ci := env.find? declName | return #[]
  let some val := ci.value? | return #[]
  let mut out : Array Name := #[]
  for c in val.getUsedConstants do
    if (`PolicyGradient).isPrefixOf c then
      out := out.push c
  return out

/-- The transitive use-set of `roots`: every `PolicyGradient` constant reachable
by repeatedly expanding proof terms. Iterated to a fixpoint. -/
def transitiveUses (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut frontier := roots
  while !frontier.isEmpty do
    let mut next : Array Name := #[]
    for n in frontier do
      for c in directUses env n do
        if !seen.contains c then
          seen := seen.insert c
          next := next.push c
    frontier := next
  return seen

/-- Run all three checks. Returns `true` if the build should fail. -/
def runPaperLint : CoreM Bool := do
  let env ← getEnv
  let claims := paperExt.getState env ++ (paperExt.toEnvExtension.getState env).importedEntries.flatten
  -- deduplicate, keep a stable order
  let mut seenDecls : NameSet := {}
  let mut all : Array PaperClaim := #[]
  for c in claims do
    if !seenDecls.contains c.decl then
      seenDecls := seenDecls.insert c.decl
      all := all.push c
  let full := all.filter (fun c => c.isFull && !c.isInfra)
  let tools := all.filter (fun c => !c.isFull && !c.isInfra)
  let infra := all.filter (·.isInfra)

  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  PAPER-CLAIM LINTER"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  -- ── Check 1: grounding ────────────────────────────────────────────────
  IO.println "── CHECK 1: grounding of @[paper] claims ──────────────────────"
  IO.println ""
  let mut ungrounded : Array PaperClaim := #[]
  let mut groundedRoots : Array Name := #[]
  let mut totalHyps : Nat := 0
  -- Witness.lean exhibits a concrete MDP satisfying the STANDING hypotheses.
  -- Anything outside that set is unwitnessed: a goal whose hypotheses are
  -- jointly contradictory is provable by `exfalso` and the census would read
  -- "proved". Tracking coverage keeps that gap visible instead of implicit.
  let witnessed : Array String := #["|M.r", "0 ≤ M.γ", "M.γ <", "Differentiable"]
  let mut unwitnessed : Nat := 0
  for c in full do
    let g ← MetaM.run' (checkGrounding c.decl)
    if g.grounded then
      groundedRoots := groundedRoots.push c.decl
      totalHyps := totalHyps + g.mdpHyps.size
      IO.println s!"[GROUNDED]   {c.decl}"
      IO.println s!"             claims: {c.paper} — {c.result}"
      if g.mdpHyps.isEmpty then
        IO.println "             MDP-level hypotheses: none"
      else
        IO.println s!"             MDP-level hypotheses ({g.mdpHyps.size}) — declared gaps:"
        for h in g.mdpHyps do
          let hs := toString h
          let cov := witnessed.any (fun w => (hs.splitOn w).length > 1)
          if cov then
            IO.println s!"               · [witnessed] {h}"
          else
            unwitnessed := unwitnessed + 1
            IO.println s!"               · [UNWITNESSED] {h}"
    else
      ungrounded := ungrounded.push c
      IO.println s!"[UNGROUNDED] {c.decl}"
      IO.println s!"             claims: {c.paper} — {c.result}"
      IO.println "             but its conclusion does not depend on any FiniteMDP binder."
      IO.println s!"             conclusion: {g.concl}"
    IO.println ""
  if full.isEmpty then
    IO.println "  (no @[paper] claims in the environment)"
    IO.println ""

  -- ── Check 2: reachability ─────────────────────────────────────────────
  IO.println "── CHECK 2: reachability of @[paper_tool] claims ──────────────"
  IO.println ""
  let reachable := transitiveUses env groundedRoots
  let mut unreached : Array PaperClaim := #[]
  for c in tools do
    if reachable.contains c.decl then
      IO.println s!"[REACHED]    {c.decl}  ({c.paper} — {c.result})"
    else
      unreached := unreached.push c
      IO.println s!"[UNREACHED]  {c.decl}  ({c.paper} — {c.result})"
      IO.println "             no @[paper]-grounded theorem uses it, even transitively."
  if tools.isEmpty then
    IO.println "  (no @[paper_tool] claims in the environment)"
  IO.println ""

  -- ── Check 3: goal census ──────────────────────────────────────────────
  -- Every frozen goal is either proved or still carries `sorry`. This is the
  -- repo's real frontier: it must only ever go down.
  IO.println "── CHECK 3: frozen-goal census ────────────────────────────────"
  IO.println ""
  let env ← getEnv
  let goals := all.filter (fun c => c.isFull || c.isInfra)
  let mut openGoals := 0
  let mut doneGoals := 0
  for c in goals do
    let axs ← collectAxioms c.decl
    let isOpen := axs.any (fun a => a == ``sorryAx)
    let tag := if c.isInfra then "infra" else "paper"
    if isOpen then
      openGoals := openGoals + 1
      IO.println s!"  [OPEN]   [{tag}] {c.decl}  ({c.paper} {c.result})"
    else
      doneGoals := doneGoals + 1
      IO.println s!"  [PROVED] [{tag}] {c.decl}  ({c.paper} {c.result})"
  IO.println ""
  IO.println s!"  frozen goals: {goals.size}   proved: {doneGoals}   OPEN: {openGoals}"
  IO.println ""

  -- ── Check 4: fidelity ─────────────────────────────────────────────────
  -- A hypothesis the proof never consumes is a signal. Either the goal is more
  -- general than intended (fine — retag it), or it has DRIFTED OFF THE PAPER
  -- (not fine). The other checks all measure a statement against its own type;
  -- this is the only one that measures it against what it claims to be.
  --
  -- Found by this check: `g2_gradient_domination`, tagged AKM Lemma 4.1, never
  -- used its softmax hypothesis — because the frozen statement had been
  -- weakened (after two refutations) into a general advantage bound with no
  -- gradient in it at all. Every other signal was green.
  IO.println "── CHECK 4: fidelity (hypotheses the proof never uses) ────────"
  IO.println ""
  let mut drifted : Nat := 0
  for c in all do
    -- Skip open goals: their `_proof` sibling may belong to a superseded
    -- statement, which would report drift against a name rather than a proof.
    let goalAxs ← collectAxioms c.decl
    if goalAxs.any (fun a => a == ``sorryAx) then continue
    let base := c.decl.componentsRev.head!
    let cand := `PolicyGradient.Proofs ++ Name.mkSimple (base.toString ++ "_proof")
    match env.find? cand with
    | some (.thmInfo ti) =>
      let unused ← MetaM.run' (lambdaTelescope ti.value fun xs body => do
        let mut u : Array Name := #[]
        for x in xs do
          let ty ← inferType x
          let nm ← x.fvarId!.getUserName
          -- instance binders are auto-generated; only named Props are signal
          if (← isProp ty) && !nm.isInternal && !(body.hasAnyFVar (· == x.fvarId!)) then
            u := u.push nm
        return u)
      if !unused.isEmpty then
        drifted := drifted + 1
        IO.println s!"  [UNUSED-HYP] {c.decl}"
        IO.println s!"               claims: {c.paper} — {c.result}"
        IO.println s!"               never used: {unused.toList}"
        IO.println "               → either retag (more general than claimed) or"
        IO.println "                 the statement has drifted off the paper."
    | _ => pure ()
  if drifted == 0 then
    IO.println "  ✓ every proved goal consumes all of its named hypotheses."
  IO.println ""

  -- ── Check 5: inhabitation ─────────────────────────────────────────────
  -- A theorem whose hypotheses can never hold is true and useless -- "every
  -- unicorn is friendly". The dangerous version is not a single goal with
  -- clashing hypotheses (that one is inert: it cannot be APPLIED anywhere,
  -- since a caller would have to supply the impossible hypotheses). It is a
  -- STRUCTURE that cannot be built: then every goal quantifying over it is
  -- vacuous at once, and no individual goal looks wrong -- its binder just
  -- reads `(F : VecPolicy ...)`.
  --
  -- So the obligation is per TYPE, not per goal, and the list is DERIVED from
  -- the goals rather than maintained by hand: whatever a frozen goal quantifies
  -- over must be demonstrably inhabited.
  IO.println "── CHECK 5: inhabitation of quantified types ──────────────────"
  IO.println ""
  let mut quantified : Array Name := #[]
  for c in all do
    let some ci := env.find? c.decl | continue
    let found ← MetaM.run' (forallTelescopeReducing ci.type fun xs _ => do
      let mut r : Array Name := #[]
      for x in xs do
        let ty ← inferType x
        if !(← isProp ty) then
          if let .const n _ := ty.getAppFn then
            if (`PolicyGradient).isPrefixOf n then r := r.push n
      return r)
    for n in found do
      if !quantified.contains n then quantified := quantified.push n
  let mut uninhabited : Nat := 0
  for n in quantified do
    -- Ask Lean itself: can `Nonempty n ..` be synthesized at the witness types
    -- from `Witness.lean` (Fin 2 states/actions)? Instance search is the right
    -- oracle here -- a name-convention scan misses real instances and reports
    -- false alarms (it did, on `Policy`, which has `instNonemptyPolicy`).
    -- Elaborate `Nonempty (n (Fin 2) (Fin 2))` from syntax rather than
    -- assembling the application by hand. The structures carry instance
    -- arguments that hand-assembly leaves as unfilled metavariables, which
    -- makes synthesis fail on types that genuinely ARE inhabited (`Policy`
    -- has `instNonemptyPolicy`, and a hand-built call still reported it as
    -- uninhabited).
    let ok ← MetaM.run' (Term.TermElabM.run' (do
      let mut found := false
      for arity in [2, 1] do
        if found then continue
        try
          let args := (List.replicate arity (← `(Fin 2))).toArray
          let head := mkIdent n
          let tyStx ← `(Nonempty ($head $args*))
          let e ← Term.elabTerm tyStx none
          let e ← instantiateMVars e
          if !e.hasExprMVar then
            let _ ← synthInstance e
            found := true
        catch _ => pure ()
      return found))
    if ok then
      IO.println s!"  [INHABITED]   {n}"
    else
      uninhabited := uninhabited + 1
      IO.println s!"  [UNINHABITED] {n}"
      IO.println "                no Nonempty instance synthesizable -- every"
      IO.println "                goal quantifying over this type may be vacuous."
  IO.println ""

  -- ── Check 6: the Formalized predicate ─────────────────────────────────
  -- Aggregate, not recompute. CHECKS 1-5 already decided every field; this
  -- reports them together so a goal's status is one verdict rather than five
  -- scattered lines. An earlier version re-ran `checkGrounding` and
  -- `forallTelescopeReducing` per claim here and segfaulted the linter --
  -- recorded because a check that crashes is indistinguishable from one that
  -- passes if its exit code is read carelessly.
  IO.println "── CHECK 6: Formalized ────────────────────────────────────────"
  IO.println ""
  IO.println s!"  fields decided above: grounded ({ungrounded.size} failing),"
  IO.println s!"  axiom-clean (see per-goal census), inhabited ({uninhabited} types failing),"
  IO.println s!"  proved ({openGoals} open -- the frontier, not a defect)."
  IO.println ""
  IO.println "  `Formalized` in Meta/Formalized.lean is the specification these"
  IO.println "  computations implement. Adding a field there re-judges every goal;"
  IO.println "  that is the point -- the free-`logits` defect was documented beside"
  IO.println "  two goals and still reached a third."
  IO.println ""

  -- ── Check 7: summary ──────────────────────────────────────────────────
  let grounded := full.size - ungrounded.size
  IO.println "── CHECK 7: summary ───────────────────────────────────────────"
  IO.println ""
  IO.println "  ┌─────────────────────────────────────────────┬───────┐"
  IO.println s!"  │ total claims                                │ {leftPad (toString all.size) 5} │"
  IO.println s!"  │   @[paper]      (full claims)               │ {leftPad (toString full.size) 5} │"
  IO.println s!"  │   @[paper_tool] (supporting machinery)      │ {leftPad (toString tools.size) 5} │"
  IO.println "  ├─────────────────────────────────────────────┼───────┤"
  IO.println s!"  │ grounded @[paper] claims                    │ {leftPad (toString grounded) 5} │"
  IO.println s!"  │ UNGROUNDED @[paper] claims  (errors)        │ {leftPad (toString ungrounded.size) 5} │"
  IO.println s!"  │ unreached @[paper_tool]     (warnings)      │ {leftPad (toString unreached.size) 5} │"
  IO.println "  ├─────────────────────────────────────────────┼───────┤"
  IO.println s!"  │ MDP-level hypotheses (the honest debt)      │ {leftPad (toString totalHyps) 5} │"
  IO.println s!"  │   of which UNWITNESSED (vacuity risk)       │ {leftPad (toString unwitnessed) 5} │"
  IO.println s!"  │ OPEN frozen goals (sorry -- the frontier)   │ {leftPad (toString openGoals) 5} │"
  IO.println s!"  │ goals with UNUSED hypotheses (drift risk)   │ {leftPad (toString drifted) 5} │"
  IO.println s!"  │ UNINHABITED quantified types (vacuity risk) │ {leftPad (toString uninhabited) 5} │"
  IO.println "  └─────────────────────────────────────────────┴───────┘"
  IO.println ""
  IO.println "  The debt number counts assumptions grounded theorems take about"
  IO.println "  the MDP rather than prove. It should only ever go down."
  IO.println ""

  if !unreached.isEmpty then
    IO.println s!"⚠  WARNING: {unreached.size} @[paper_tool] claim(s) unreached (not fatal yet)."
    IO.println ""
  if !ungrounded.isEmpty then
    IO.println s!"✗  FAILED: {ungrounded.size} @[paper] claim(s) are ungrounded."
    IO.println "   A @[paper] claim must be about an actual FiniteMDP. Either ground"
    IO.println "   the statement, or downgrade the annotation to @[paper_tool]."
    IO.println ""
    return true
  IO.println "✓  PASSED: every @[paper] claim is grounded in a FiniteMDP."
  IO.println ""
  return false
where
  /-- Right-align `s` in a field of width `w`. -/
  leftPad (s : String) (w : Nat) : String :=
    "".pushn ' ' (w - min w s.length) ++ s

end PolicyGradient.Meta
