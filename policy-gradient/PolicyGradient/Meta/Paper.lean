import Lean
open Lean

/-- `@[paper "Mei2020" "Theorem 4"]` records that a declaration formalizes a
named result from a named paper. -/
syntax (name := paperAttr) "paper" str str : attr

initialize paperExt :
    SimplePersistentEnvExtension (Name × String × String) (Array (Name × String × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (init := #[]) (· ++ ·)
  }

initialize registerBuiltinAttribute {
  name := `paperAttr
  descr := "marks a theorem as formalizing a named paper result"
  add := fun decl stx _ => do
    let paper := stx[1].isStrLit?.getD ""
    let result := stx[2].isStrLit?.getD ""
    modifyEnv (paperExt.addEntry · (decl, paper, result))
}
