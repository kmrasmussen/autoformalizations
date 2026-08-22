/-
Copyright (c) 2026. Released under Apache 2.0 license.

Entry point for the paper-claim linter. Run with `lake exe paper_lint`.

Importing the whole `PolicyGradient` library is what populates the environment
extension with every `@[paper]` / `@[paper_tool]` annotation in the repo; the
linter then reads them back out.
-/
import PolicyGradient
import PolicyGradient.Meta.Lint

open Lean

/-- The linter proper.

`enableInitializersExecution` is what makes the printed hypotheses readable:
notation delaborators (`≤` rather than `Real.instLE.le`) are installed by module
initializers, which do not run for imported modules unless this is set. It is an
`unsafe` primitive, hence the `unsafe def` + `@[implemented_by]` wrapper below —
the standard pattern for a Lean program that imports its own library. -/
unsafe def lint : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules
    #[{ module := `PolicyGradient }, { module := `PolicyGradient.Meta.Lint }]
    (opts := {}) (trustLevel := 1024)
  -- `pp.fullNames := false` + the standard notation options are what make the
  -- printed hypotheses read like the source (`≤`, `|·|`, `∑`) rather than like
  -- raw application spines. They must be set in the `Core.Context`, since the
  -- pretty-printer reads them from there.
  let opts : Options := (({} : Options)
    |>.setBool `pp.fullNames false)
    |>.setBool `pp.notation true
  let (failed, _) ← Core.CoreM.toIO
    PolicyGradient.Meta.runPaperLint
    { fileName := "<paper_lint>", fileMap := default, options := opts }
    { env := env }
  return if failed then 1 else 0

@[implemented_by lint]
opaque lintImpl : IO UInt32

def main : IO UInt32 := lintImpl
