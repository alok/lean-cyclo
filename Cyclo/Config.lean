import Lean

/-!
# Cyclomatic Complexity Linter Configuration

Defines the Lean `set_option` knobs and runtime `Config` structure used by both
the live Lean 4 command linter (`import Cyclo`) and the standalone `cyclo` CLI.
-/

namespace Cyclo

open Lean

/-- Enable the AI-first cyclomatic complexity linter. -/
register_option linter.cyclo : Bool := {
  defValue := true
  descr := "enable the AI-first cyclomatic complexity linter"
}

/-- Maximum cyclomatic complexity allowed for code declarations (`def`, `abbrev`, `instance`, etc.). -/
register_option linter.cyclo.threshold : Nat := {
  defValue := 10
  descr := "maximum cyclomatic complexity for code declarations before warning"
}

/-- Maximum cyclomatic complexity allowed for proofs (`theorem`). -/
register_option linter.cyclo.proofThreshold : Nat := {
  defValue := 15
  descr := "maximum cyclomatic complexity for theorem/proof declarations before warning"
}

/-- Whether to lint `theorem` declarations in addition to code declarations. -/
register_option linter.cyclo.includeProofs : Bool := {
  defValue := true
  descr := "whether to analyze cyclomatic complexity of theorem declarations"
}

/-- Optional maximum branch nesting depth trigger (0 = advisory only, never triggers alone). -/
register_option linter.cyclo.maxDepth : Nat := {
  defValue := 0
  descr := "optional maximum branch nesting depth before warning (0 disables standalone depth warnings)"
}

/-- Discount flat, single-level enum/constructor dispatch (`match` or equation arms at depth <= 1). -/
register_option linter.cyclo.flatMatchDiscount : Bool := {
  defValue := false
  descr := "count a flat top-level match/equation dispatch as +1 instead of +(k-1)"
}

/-- Emit a structured JSON payload inside each diagnostic for AI harnesses and CI tools. -/
register_option linter.cyclo.json : Bool := {
  defValue := false
  descr := "append a machine-readable JSON block to each cyclomatic complexity diagnostic"
}

/-- Report complexity metrics as info messages for every declaration (useful for codebase audits). -/
register_option linter.cyclo.reportAll : Bool := {
  defValue := false
  descr := "emit info-level complexity diagnostics for every declaration, even below threshold"
}

/-- Pure runtime configuration shared between the Lean linter and the standalone CLI. -/
structure Config where
  /-- Threshold for non-proof declarations (`def`, `abbrev`, `instance`, etc.). -/
  threshold : Nat := 10
  /-- Threshold for `theorem` declarations. -/
  proofThreshold : Nat := 15
  /-- Whether to analyze `theorem` declarations. -/
  includeProofs : Bool := true
  /-- Optional standalone nesting-depth trigger (`0` = disabled). -/
  maxDepth : Nat := 0
  /-- If `true`, flat top-level `match` / equation tables are discounted to `+1`. -/
  flatMatchDiscount : Bool := false
  /-- Append JSON block to text diagnostics. -/
  emitJson : Bool := false
  /-- Emit info diagnostics even for declarations within budget. -/
  reportAll : Bool := false
  deriving Repr, Inhabited, BEq

/-- Read `Config` from Lean's current `Options`. -/
def Config.fromOptions (opts : Options) : Config := {
  threshold := linter.cyclo.threshold.get opts
  proofThreshold := linter.cyclo.proofThreshold.get opts
  includeProofs := linter.cyclo.includeProofs.get opts
  maxDepth := linter.cyclo.maxDepth.get opts
  flatMatchDiscount := linter.cyclo.flatMatchDiscount.get opts
  emitJson := linter.cyclo.json.get opts
  reportAll := linter.cyclo.reportAll.get opts
}

end Cyclo
