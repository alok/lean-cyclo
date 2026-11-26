import Lean
import Cyclo.Config
import Cyclo.Metrics
import Cyclo.Analyzer
import Cyclo.Diagnostics

/-!
# Lean 4 Native Command Linter (`import Cyclo`)

Registers `cycloLinter` with Lean 4's command linter pipeline using
`Lean.Linter.logLint`, so warnings appear inline in editors, `lake build`,
`lean-lsp-mcp`, and `#guard_msgs` tests.

Usage:
```lean
import Cyclo
```
Disable locally:
```lean
set_option linter.cyclo false in
def myComplexFn ...
```
-/

namespace Cyclo

open Lean Elab Command
open Lean.Linter (getLinterValue getLinterOptions logLint)

/-- Run the cyclomatic complexity linter on a single elaborated command. -/
def cycloLinterRun (stx : Syntax) : CommandElabM Unit := do
  let linterOpts ← getLinterOptions
  let baseEnabled := getLinterValue linter.cyclo linterOpts
  let baseCfg := Config.fromOptions (← getOptions)
  let (enabled, cfg, innerStx) := unwrapInCommand baseEnabled baseCfg stx
  unless enabled do
    return
  let fileName ← getFileName
  let fileMap ← getFileMap
  let currNs ← getCurrNamespace
  let nsPrefix := if currNs.isAnonymous then "" else currNs.toString
  let reports := analyzeCommand cfg fileName fileMap innerStx nsPrefix
  for r in reports do
    if r.isWarning then
      logLint linter.cyclo r.anchorStx (formatLinterMessage r cfg.emitJson)
    else if cfg.reportAll then
      let msg :=
        if cfg.emitJson then
          s!"{formatInfoSummary r}\nJSON: {(toJson r).compress}"
        else
          formatInfoSummary r
      logInfoAt r.anchorStx msg

/-- The Lean 4 `Linter` instance for cyclomatic complexity. -/
def cycloLinter : Linter where
  run := cycloLinterRun
  name := `Cyclo.cycloLinter

initialize addLinter cycloLinter

end Cyclo
