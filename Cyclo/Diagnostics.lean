import Lean
import Cyclo.Metrics

/-!
# AI-First Diagnostic Formatters

Produces concise, deterministic, high-signal diagnostics tailored for AI coding
agents as well as human Lean 4 developers:
- Zero filler prose; front-loaded metrics (`CC`, `threshold`, `max_depth`, `pattern`).
- Exact `L<line>:<col>` hotspot attribution sorted by McCabe delta.
- Tailored Lean-idiomatic refactoring recipes (not generic boilerplate).
- Copy-pasteable local suppression / threshold-override snippets.
- First-class `--format json` and `--format agent` outputs.
-/

namespace Cyclo

open Lean

private def formatBreakdownLine (b : CategoryBreakdown) : String :=
  let parts : Array String := Id.run do
    let mut ps : Array String := #[]
    if b.term > 0 then ps := ps.push s!"term:+{b.term}"
    if b.doControl > 0 then ps := ps.push s!"do:+{b.doControl}"
    if b.boolean > 0 then ps := ps.push s!"bool:+{b.boolean}"
    if b.errorHandling > 0 then ps := ps.push s!"err:+{b.errorHandling}"
    if b.tactic > 0 then ps := ps.push s!"tactic:+{b.tactic}"
    return ps
  if parts.isEmpty then "none" else String.intercalate ", " parts.toList

private def formatHotspotLine (idx : Nat) (dp : DecisionPoint) : String :=
  let loc := if dp.line > 0 then s!"L{dp.line}:{dp.col}" else "L?"
  s!"  {idx}. {loc}  +{dp.delta}  {dp.kind.label} [depth {dp.depth}]"

/-- Format a compact one-line info summary (used when `linter.cyclo.reportAll` is enabled for OK decls). -/
def formatInfoSummary (r : DeclReport) : String :=
  let ccStr :=
    if r.effectiveComplexity == r.complexity then s!"{r.complexity}"
    else s!"{r.effectiveComplexity} (raw {r.complexity})"
  s!"[cyclo] `{r.name}` ({r.kind}) CC={ccStr}/{r.threshold}, max_depth={r.maxDepth}, pattern={r.pattern}, breakdown=[{formatBreakdownLine r.breakdown}]"

/-- Format a rich, AI-first Lean diagnostic message for a declaration exceeding budget. -/
def formatLinterMessage (r : DeclReport) (emitJson : Bool := false) : String := Id.run do
  let ccDisplay :=
    if r.effectiveComplexity == r.complexity then s!"{r.complexity}"
    else s!"{r.effectiveComplexity} (raw {r.complexity})"
  let header :=
    s!"[cyclo] `{r.name}` ({r.kind}) cyclomatic complexity = {ccDisplay} " ++
    s!"(threshold: {r.threshold}, max_depth: {r.maxDepth}, pattern: {r.pattern})"
  let mut lines : Array String := #[header]

  if !r.triggers.isEmpty then
    lines := lines.push s!"Triggered: {String.intercalate "; " r.triggers.toList}"

  let totalDelta := r.complexity - 1
  lines := lines.push s!"Breakdown (+{totalDelta} decision points): {formatBreakdownLine r.breakdown}"

  let hotspots := r.topHotspots 5
  if !hotspots.isEmpty then
    lines := lines.push "Hotspots:"
    for i in [:hotspots.size] do
      lines := lines.push (formatHotspotLine (i + 1) hotspots[i]!)

  if !r.suggestions.isEmpty then
    lines := lines.push "Refactor options:"
    for s in r.suggestions do
      lines := lines.push s!"  - [{s.id}] {s.action}"
      lines := lines.push s!"    Impact: {s.impact}"

  let optName := if r.kind.isProof then "linter.cyclo.proofThreshold" else "linter.cyclo.threshold"
  lines := lines.push s!"Local override: `set_option {optName} {r.effectiveComplexity} in` or `set_option linter.cyclo false in`"

  if emitJson then
    lines := lines.push s!"JSON: {(toJson r).compress}"

  return String.intercalate "\n" lines.toList

/-- Filter and rank declaration reports for CLI output (`agent`, `text`, and `json`). -/
def selectReports (reports : Array DeclReport) (showAll : Bool)
    (topN : Option Nat) : Array DeclReport :=
  let filtered := if showAll then reports else reports.filter (·.isWarning)
  let sorted := filtered.qsort fun a b =>
    if a.isWarning != b.isWarning then a.isWarning
    else if a.effectiveComplexity != b.effectiveComplexity then a.effectiveComplexity > b.effectiveComplexity
    else if a.maxDepth != b.maxDepth then a.maxDepth > b.maxDepth
    else a.file < b.file || (a.file == b.file && a.line < b.line)
  match topN with
  | some n => sorted.extract 0 (min n sorted.size)
  | none => sorted

/-- Token-efficient, structured brief designed for AI coding agents running `cyclo` in a loop. -/
def formatAgentBrief (summary : ScanSummary) (showAll : Bool := false)
    (topN : Option Nat := none) : String := Id.run do
  let selected := selectReports summary.reports showAll topN
  let status := if summary.warningsCount == 0 && summary.parseErrors.isEmpty then "PASS" else "WARN"
  let mut lines : Array String := #[
    s!"CYCLO {status} | files={summary.filesScanned} decls={summary.declarationsAnalyzed} warnings={summary.warningsCount} max_cc={summary.maxComplexity}"
  ]

  for err in summary.parseErrors do
    lines := lines.push s!"PARSE_ERROR {err}"

  if selected.isEmpty then
    if summary.warningsCount == 0 then
      lines := lines.push "All analyzed declarations are within cyclomatic complexity budgets."
    return String.intercalate "\n" lines.toList

  for r in selected do
    let sev := if r.isWarning then "WARN" else "OK"
    let loc := s!"{r.file}:{r.line}:{r.col}"
    lines := lines.push ""
    lines := lines.push s!"{sev} {loc} `{r.name}` ({r.kind}) CC={r.effectiveComplexity}/{r.threshold} depth={r.maxDepth} lines={r.lineCount} pattern={r.pattern}"
    lines := lines.push s!"  breakdown: {formatBreakdownLine r.breakdown}"
    let hotspots := r.topHotspots 4
    if !hotspots.isEmpty then
      let hs := hotspots.toList.map fun dp =>
        s!"L{dp.line}:{dp.col} +{dp.delta} {dp.kind.label} (d{dp.depth})"
      lines := lines.push s!"  hotspots: {String.intercalate " | " hs}"
    for s in r.suggestions.extract 0 (min 2 r.suggestions.size) do
      lines := lines.push s!"  fix[{s.id}]: {s.action}"

  return String.intercalate "\n" lines.toList

/-- Human-oriented terminal summary report. -/
def formatTextReport (summary : ScanSummary) (showAll : Bool := false)
    (topN : Option Nat := none) : String := Id.run do
  let selected := selectReports summary.reports showAll topN
  let mut lines : Array String := #[
    s!"lean-cyclo: scanned {summary.filesScanned} file(s), {summary.declarationsAnalyzed} declaration(s), {summary.warningsCount} warning(s), max CC = {summary.maxComplexity}"
  ]
  for err in summary.parseErrors do
    lines := lines.push s!"error: {err}"

  for r in selected do
    lines := lines.push ""
    if r.isWarning then
      lines := lines.push s!"{r.file}:{r.line}:{r.col}:"
      lines := lines.push (formatLinterMessage r (emitJson := false))
    else
      lines := lines.push s!"{r.file}:{r.line}:{r.col}: {formatInfoSummary r}"

  return String.intercalate "\n" lines.toList

end Cyclo
