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

/-- A recorded paper claim: declaration, paper key, result name. -/
structure PaperClaim where
  decl : Name
  paper : String
  result : String
  /-- `true` for `@[paper]`, `false` for `@[paper_tool]`. -/
  isFull : Bool
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
    modifyEnv (paperExt.addEntry · ⟨decl, paper, result, true⟩)
}

initialize registerBuiltinAttribute {
  name := `paperToolAttr
  descr := "this declaration is machinery supporting the named paper result"
  add := fun decl stx _ => do
    let paper := stx[1].isStrLit?.getD ""
    let result := stx[2].isStrLit?.getD ""
    modifyEnv (paperExt.addEntry · ⟨decl, paper, result, false⟩)
}
