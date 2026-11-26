import Lean
import Cyclo

/-!
# `cyclo` CLI & Lake Lint Driver

Run directly via `lake exe cyclo [OPTIONS] [PATHS...]` or as a Lake lint driver
via `lake lint`. Defaults to token-efficient `--format agent` output designed
for AI coding loops, with `--format json` for structured pipelines and
`--format text` for human terminals.
-/

open Cyclo

private inductive OutputFormat where
  | agent
  | text
  | json
  deriving BEq, Inhabited

private structure CliOptions where
  cfg : Config := {}
  format : OutputFormat := .agent
  showAll : Bool := false
  topN : Option Nat := none
  failOnWarn : Bool := true
  showHelp : Bool := false
  paths : Array System.FilePath := #[]
  deriving Inhabited

private def helpText : String :=
  "lean-cyclo — AI-first cyclomatic complexity linter for Lean 4\n\n" ++
  "USAGE:\n" ++
  "  lake exe cyclo [OPTIONS] [PATHS...]\n" ++
  "  lake lint -- [OPTIONS] [PATHS...]\n\n" ++
  "OPTIONS:\n" ++
  "  --format <agent|text|json>   Output format (default: agent)\n" ++
  "  --json                       Shorthand for --format json\n" ++
  "  --threshold <N>              Max CC for code decls (default: 10)\n" ++
  "  --proof-threshold <N>        Max CC for theorems (default: 15)\n" ++
  "  --max-depth <N>              Standalone max nesting depth trigger (default: 0 = off)\n" ++
  "  --no-proofs                  Skip theorem declarations\n" ++
  "  --flat-match-discount        Discount flat top-level match/equation tables to +1\n" ++
  "  --all                        Include declarations within budget\n" ++
  "  --top <N>                    Show only the top N highest-complexity declarations\n" ++
  "  --no-fail                    Exit 0 even when warnings are found (audit mode)\n" ++
  "  -h, --help                   Show this help message\n"

private def parseNatArg (flag val : String) : Except String Nat :=
  match val.toNat? with
  | some n => .ok n
  | none => .error s!"{flag} expects a non-negative integer, got `{val}`"

private def parseFormat (val : String) : Except String OutputFormat :=
  match val with
  | "agent" => .ok .agent
  | "text" => .ok .text
  | "json" => .ok .json
  | other => .error s!"unknown format `{other}` (expected: agent, text, json)"

private def applyBoolFlag (flag : String) (opts : CliOptions) : Option CliOptions :=
  match flag with
  | "-h" | "--help" => some { opts with showHelp := true }
  | "--json" => some { opts with format := .json }
  | "--no-proofs" => some { opts with cfg := { opts.cfg with includeProofs := false } }
  | "--flat-match-discount" => some { opts with cfg := { opts.cfg with flatMatchDiscount := true } }
  | "--all" => some { opts with showAll := true }
  | "--no-fail" => some { opts with failOnWarn := false }
  | _ => none

private def applyValueFlag (flag val : String) (opts : CliOptions) : Option (Except String CliOptions) :=
  match flag with
  | "--format" => some do
    let fmt ← parseFormat val
    return { opts with format := fmt }
  | "--threshold" => some do
    let n ← parseNatArg "--threshold" val
    return { opts with cfg := { opts.cfg with threshold := n } }
  | "--proof-threshold" => some do
    let n ← parseNatArg "--proof-threshold" val
    return { opts with cfg := { opts.cfg with proofThreshold := n } }
  | "--max-depth" => some do
    let n ← parseNatArg "--max-depth" val
    return { opts with cfg := { opts.cfg with maxDepth := n } }
  | "--top" => some do
    let n ← parseNatArg "--top" val
    return { opts with topN := some n }
  | _ => none

private def parseCli (args : List String) : Except String CliOptions :=
  go args {}
where
  go (xs : List String) (opts : CliOptions) : Except String CliOptions :=
    match xs with
    | [] => .ok opts
    | arg :: rest =>
      if let some next := applyBoolFlag arg opts then
        if next.showHelp then .ok next else go rest next
      else match rest with
      | val :: tail =>
        if let some res := applyValueFlag arg val opts then do
          go tail (← res)
        else if arg.startsWith "-" then
          .error s!"unknown option `{arg}` (run with --help)"
        else
          go (val :: tail) { opts with paths := opts.paths.push (System.FilePath.mk arg) }
      | [] =>
        if arg.startsWith "-" then
          .error s!"unknown or incomplete option `{arg}` (run with --help)"
        else
          .ok { opts with paths := opts.paths.push (System.FilePath.mk arg) }
  termination_by xs.length

def main (args : List String) : IO UInt32 := do
  match parseCli args with
  | .error err =>
    IO.eprintln s!"lean-cyclo: {err}"
    return 2
  | .ok opts =>
    if opts.showHelp then
      IO.println helpText
      return 0
    let targetPaths := if opts.paths.isEmpty then #[System.FilePath.mk "."] else opts.paths
    let summary ← scanPaths opts.cfg targetPaths
    match opts.format with
    | .json =>
      let filtered := { summary with reports := selectReports summary.reports opts.showAll opts.topN }
      IO.println (Lean.toJson filtered).pretty
    | .agent => IO.println (formatAgentBrief summary opts.showAll opts.topN)
    | .text => IO.println (formatTextReport summary opts.showAll opts.topN)
    if opts.failOnWarn && (summary.warningsCount > 0 || !summary.parseErrors.isEmpty) then
      return 1
    return 0
