/-
Copyright (c) 2026. Released under Apache 2.0 license.

Entry point for the paper-claim linter:

    lake env lean PaperLint.lean

Importing the whole `PolicyGradient` library is what populates the environment
extension with every `@[paper]` / `@[paper_tool]` annotation in the repo; the
linter then reads them back out.

Why a `lean` file rather than only the `paper_lint` executable: the linter
prints hypotheses with `ppExpr`, and Mathlib's notation delaborators (`≤`, `|·|`,
`∑`) are installed by module initializers that a *compiled* program's
`importModules` does not run. Under `lake env lean` they are all present, so the
declared gaps print exactly as they read in the source file. `lake exe
paper_lint` performs the identical checks and is equally valid for pass/fail;
only the rendering of the hypotheses is more verbose there.

A failing check is reported as a Lean error, so this exits nonzero.
-/
import PolicyGradient
import PolicyGradient.Goal
import PolicyGradient.Meta.Lint

open Lean

#eval show CoreM Unit from do
  let failed ← PolicyGradient.Meta.runPaperLint
  if failed then
    throwError "paper-claim linter: ungrounded @[paper] claim(s) — see [UNGROUNDED] above"
