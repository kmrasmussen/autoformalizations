/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Lean

/-!
# Paper-claim attributes

Machine-readable claims that a declaration formalizes a named paper result.

The point is that a docstring saying "this is Mei Theorem 4" is invisible to the
build, so it can drift arbitrarily far from what the theorem states — which is
exactly what happened here (see `GAPS.md`). These attributes make the claim
checkable.

* `@[paper "Mei2020" "Theorem 4"]` — *this is* the paper's result. The linter
  requires its conclusion to actually say something about a `FiniteMDP`.
* `@[paper_tool "Mei2020" "Theorem 4"]` — *machinery for* the paper's result.
  Abstract lemmas are legitimate and valuable; this asserts support, never
  identity.
-/

open Lean

/-- `@[paper "Mei2020" "Theorem 4"]`: this declaration *is* that paper result. -/
syntax (name := paperAttr) "paper" str str : attr

/-- `@[paper_tool "Mei2020" "Theorem 4"]`: machinery supporting that result. -/
syntax (name := paperToolAttr) "paper_tool" str str : attr

/-- `@[infra "G5"]`: an infrastructure goal — an object that must be *built*.

Not a paper result, so the grounding check does not apply: its conclusion is an
existence claim, which is precisely why it cannot be weakened by adding
hypotheses (the payload is the object). Tracked separately in the census. -/
syntax (name := infraAttr) "infra" str : attr

/-- A recorded paper claim: declaration, paper key, result name. -/
structure PaperClaim where
  decl : Name
  paper : String
  result : String
  /-- `true` for `@[paper]`, `false` for `@[paper_tool]`. -/
  isFull : Bool
  /-- `true` for `@[infra]`: an object-construction goal, exempt from grounding. -/
  isInfra : Bool := false
  /-- Constants the paper result is *about*, which its conclusion must mention.

  A statement tagged AKM Lemma 4.1 whose conclusion contains no derivative is
  not that lemma, however true it may be — this is what caught
  `g2_advantage_bound`. Declared as `@[paper "AKM2021" "Lemma 4.1" subject fderiv]`. -/
  subject : Array Name := #[]
  deriving Inhabited

initialize paperExt :
    SimplePersistentEnvExtension PaperClaim (Array PaperClaim) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (init := #[]) (· ++ ·)
  }

initialize registerBuiltinAttribute {
  name := `paperAttr
  descr := "this declaration formalizes the named paper result"
  add := fun decl stx _ => do
    let paper := stx[1].isStrLit?.getD ""
    let result := stx[2].isStrLit?.getD ""
    modifyEnv (paperExt.addEntry · ⟨decl, paper, result, true, false, #[]⟩)
}

initialize registerBuiltinAttribute {
  name := `infraAttr
  descr := "an infrastructure goal: an object that must be constructed"
  add := fun decl stx _ => do
    let result := stx[1].isStrLit?.getD ""
    modifyEnv (paperExt.addEntry · ⟨decl, "Infrastructure", result, false, true, #[]⟩)
}

initialize registerBuiltinAttribute {
  name := `paperToolAttr
  descr := "this declaration is machinery supporting the named paper result"
  add := fun decl stx _ => do
    let paper := stx[1].isStrLit?.getD ""
    let result := stx[2].isStrLit?.getD ""
    modifyEnv (paperExt.addEntry · ⟨decl, paper, result, false, false, #[]⟩)
}
