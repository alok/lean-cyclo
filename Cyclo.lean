import Cyclo.Config
import Cyclo.Metrics
import Cyclo.Analyzer
import Cyclo.Diagnostics
import Cyclo.Linter
import Cyclo.Scanner

/-!
# `lean-cyclo` — AI-First Cyclomatic Complexity Linter for Lean 4

Importing `Cyclo` activates the native Lean 4 command linter (`linter.cyclo`)
and exposes the programmatic complexity analysis, diagnostic formatting, and
standalone file-scanning APIs.
-/
