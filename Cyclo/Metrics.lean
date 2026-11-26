import Lean
import Cyclo.Config

/-!
# Cyclomatic Complexity Data Model

Pure, serializable data types representing Lean 4 decision points, diagnosed
complexity patterns, actionable refactoring suggestions, and declaration/file
reports. All types implement `ToJson` so AI agents and CI tools can consume them
without parsing prose.
-/

namespace Cyclo

open Lean

/-- High-level category of a branching construct in Lean 4. -/
inductive BranchCategory where
  | term
  | doControl
  | boolean
  | errorHandling
  | tactic
  deriving Repr, Inhabited, BEq, DecidableEq

def BranchCategory.toString : BranchCategory → String
  | .term => "term"
  | .doControl => "do-control"
  | .boolean => "boolean"
  | .errorHandling => "error-handling"
  | .tactic => "tactic"

instance : ToString BranchCategory := ⟨BranchCategory.toString⟩
instance : ToJson BranchCategory := ⟨fun c => Json.str c.toString⟩

/-- Specific Lean 4 syntax construct that adds to cyclomatic complexity. -/
inductive BranchKind where
  | ifExpr
  | depIfExpr
  | ifLetExpr
  | elseIfBranch
  | matchArms (arms : Nat)
  | equationAlts (arms : Nat)
  | doIf
  | doUnless
  | doFor
  | doWhile
  | doRepeat
  | doLetElse
  | tryCatch
  | tryCatchMatch (arms : Nat)
  | boolAnd
  | boolOr
  | orElse
  | tacticCases (arms : Nat)
  | tacticInduction (arms : Nat)
  | tacticSplit
  | tacticByCases
  | tacticFirst (arms : Nat)
  | tacticTry
  | tacticRepeat
  | tacticOrElse
  | tacticMatch (arms : Nat)
  deriving Repr, Inhabited, BEq

def BranchKind.category : BranchKind → BranchCategory
  | .ifExpr | .depIfExpr | .ifLetExpr | .elseIfBranch
  | .matchArms _ | .equationAlts _ => .term
  | .doIf | .doUnless | .doFor | .doWhile | .doRepeat => .doControl
  | .boolAnd | .boolOr | .orElse => .boolean
  | .doLetElse | .tryCatch | .tryCatchMatch _ => .errorHandling
  | .tacticCases _ | .tacticInduction _ | .tacticSplit | .tacticByCases
  | .tacticFirst _ | .tacticTry | .tacticRepeat | .tacticOrElse
  | .tacticMatch _ => .tactic

private def fmtTacticCount (name : String) (k : Nat) : String :=
  if k > 0 then s!"{name} ({k} alts)" else name

set_option linter.cyclo.flatMatchDiscount true in
def BranchKind.label : BranchKind → String
  | .ifExpr => "if/then/else"
  | .depIfExpr => "if h : ... then/else"
  | .ifLetExpr => "if let"
  | .elseIfBranch => "else if"
  | .matchArms k => s!"match ({k} arms)"
  | .equationAlts k => s!"equation arms ({k} cases)"
  | .doIf => "do if"
  | .doUnless => "unless"
  | .doFor => "for loop"
  | .doWhile => "while loop"
  | .doRepeat => "repeat loop"
  | .doLetElse => "let ... | fallback"
  | .tryCatch => "try/catch"
  | .tryCatchMatch k => s!"try/catch ({k} arms)"
  | .boolAnd => "&&"
  | .boolOr => "||"
  | .orElse => "<|>"
  | .tacticCases k => fmtTacticCount "cases" k
  | .tacticInduction k => fmtTacticCount "induction" k
  | .tacticSplit => "split"
  | .tacticByCases => "by_cases"
  | .tacticFirst k => s!"first ({k} tactics)"
  | .tacticTry => "try tactic"
  | .tacticRepeat => "repeat tactic"
  | .tacticOrElse => "tactic <|>"
  | .tacticMatch k => s!"tactic match ({k} arms)"

set_option linter.cyclo.flatMatchDiscount true in
def BranchKind.kindKey : BranchKind → String
  | .ifExpr => "if"
  | .depIfExpr => "dep_if"
  | .ifLetExpr => "if_let"
  | .elseIfBranch => "else_if"
  | .matchArms _ => "match"
  | .equationAlts _ => "equations"
  | .doIf => "do_if"
  | .doUnless => "unless"
  | .doFor => "for"
  | .doWhile => "while"
  | .doRepeat => "repeat"
  | .doLetElse => "let_else"
  | .tryCatch => "try_catch"
  | .tryCatchMatch _ => "try_catch_match"
  | .boolAnd => "bool_and"
  | .boolOr => "bool_or"
  | .orElse => "or_else"
  | .tacticCases _ => "tactic_cases"
  | .tacticInduction _ => "tactic_induction"
  | .tacticSplit => "tactic_split"
  | .tacticByCases => "tactic_by_cases"
  | .tacticFirst _ => "tactic_first"
  | .tacticTry => "tactic_try"
  | .tacticRepeat => "tactic_repeat"
  | .tacticOrElse => "tactic_orelse"
  | .tacticMatch _ => "tactic_match"

/-- A single decision point inside a declaration body. -/
structure DecisionPoint where
  kind : BranchKind
  /-- McCabe complexity contribution (`>= 1`). -/
  delta : Nat
  /-- 1-indexed nesting depth of this decision point inside the declaration. -/
  depth : Nat
  /-- 1-indexed source line number (`0` if synthetic). -/
  line : Nat
  /-- 1-indexed source column number (`0` if synthetic). -/
  col : Nat
  /-- Optional end line of the syntax span for extraction hints. -/
  endLine : Nat
  deriving Repr, Inhabited, BEq

instance : ToJson DecisionPoint where
  toJson dp := Json.mkObj [
    ("kind", Json.str dp.kind.kindKey),
    ("label", Json.str dp.kind.label),
    ("category", toJson dp.kind.category),
    ("delta", toJson dp.delta),
    ("depth", toJson dp.depth),
    ("line", toJson dp.line),
    ("col", toJson dp.col),
    ("endLine", toJson dp.endLine)
  ]

/-- Declaration flavor analyzed by the linter. -/
inductive DeclKind where
  | definition
  | abbrevDecl
  | theoremDecl
  | instanceDecl
  | opaqueDecl
  | exampleDecl
  | whereHelper
  deriving Repr, Inhabited, BEq, DecidableEq

def DeclKind.toString : DeclKind → String
  | .definition => "def"
  | .abbrevDecl => "abbrev"
  | .theoremDecl => "theorem"
  | .instanceDecl => "instance"
  | .opaqueDecl => "opaque"
  | .exampleDecl => "example"
  | .whereHelper => "where"

def DeclKind.isProof : DeclKind → Bool
  | .theoremDecl => true
  | _ => false

instance : ToString DeclKind := ⟨DeclKind.toString⟩
instance : ToJson DeclKind := ⟨fun k => Json.str k.toString⟩

/-- Root-cause complexity archetype diagnosed from the decision-point distribution. -/
inductive ComplexityPattern where
  | flatDispatch
  | deepNesting
  | booleanSoup
  | imperativeLoopNest
  | errorHandlingHeavy
  | tacticExplosion
  | mixedBranching
  deriving Repr, Inhabited, BEq, DecidableEq

def ComplexityPattern.toString : ComplexityPattern → String
  | .flatDispatch => "flat-dispatch"
  | .deepNesting => "deep-nesting"
  | .booleanSoup => "boolean-soup"
  | .imperativeLoopNest => "imperative-loop-nest"
  | .errorHandlingHeavy => "error-handling-heavy"
  | .tacticExplosion => "tactic-explosion"
  | .mixedBranching => "mixed-branching"

instance : ToString ComplexityPattern := ⟨ComplexityPattern.toString⟩
instance : ToJson ComplexityPattern := ⟨fun p => Json.str p.toString⟩

/-- Severity classification for a declaration report. -/
inductive Severity where
  | ok
  | warning
  deriving Repr, Inhabited, BEq, DecidableEq

def Severity.toString : Severity → String
  | .ok => "ok"
  | .warning => "warning"

instance : ToString Severity := ⟨Severity.toString⟩
instance : ToJson Severity := ⟨fun s => Json.str s.toString⟩

/-- A concrete, Lean-idiomatic refactoring action tailored to a declaration's hotspots. -/
structure RefactorSuggestion where
  /-- Short machine-friendly identifier for the strategy (e.g. `extract-where-helper`). -/
  id : String
  /-- Imperative one-line refactoring instruction referencing exact lines when available. -/
  action : String
  /-- Brief explanation of why this reduces cognitive/branching load. -/
  impact : String
  deriving Repr, Inhabited, BEq

instance : ToJson RefactorSuggestion where
  toJson s := Json.mkObj [
    ("id", Json.str s.id),
    ("action", Json.str s.action),
    ("impact", Json.str s.impact)
  ]

/-- Per-category decision-point breakdown. -/
structure CategoryBreakdown where
  term : Nat := 0
  doControl : Nat := 0
  boolean : Nat := 0
  errorHandling : Nat := 0
  tactic : Nat := 0
  deriving Repr, Inhabited, BEq

instance : ToJson CategoryBreakdown where
  toJson b := Json.mkObj [
    ("term", toJson b.term),
    ("doControl", toJson b.doControl),
    ("boolean", toJson b.boolean),
    ("errorHandling", toJson b.errorHandling),
    ("tactic", toJson b.tactic)
  ]

/-- Full cyclomatic complexity analysis for one declaration (or `where` helper). -/
structure DeclReport where
  /-- File path (populated by CLI scanner or command linter). -/
  file : String
  /-- Declaration name (or `<anonymous>` / `parent.helper`). -/
  name : String
  /-- Kind of Lean declaration. -/
  kind : DeclKind
  /-- Raw McCabe cyclomatic complexity (`1 + sum(decisionPoints.delta)`). -/
  complexity : Nat
  /-- Effective complexity after optional `flatMatchDiscount`. -/
  effectiveComplexity : Nat
  /-- Active complexity budget for this declaration. -/
  threshold : Nat
  /-- Maximum branch nesting depth observed inside the body. -/
  maxDepth : Nat
  /-- Active standalone nesting-depth budget (`0` = advisory only). -/
  maxDepthThreshold : Nat
  /-- 1-indexed start line. -/
  line : Nat
  /-- 1-indexed start column. -/
  col : Nat
  /-- 1-indexed end line. -/
  endLine : Nat
  /-- Diagnosed structural complexity pattern. -/
  pattern : ComplexityPattern
  /-- Whether complexity or nesting budget was exceeded. -/
  severity : Severity
  /-- Why this report triggered (empty if `severity == .ok`). -/
  triggers : Array String
  /-- Breakdown of decision points by Lean construct category. -/
  breakdown : CategoryBreakdown
  /-- All decision points found inside the body. -/
  decisionPoints : Array DecisionPoint
  /-- Concrete, tailored refactoring recipes. -/
  suggestions : Array RefactorSuggestion
  /-- Syntax node to attach LSP diagnostics to (not serialized). -/
  anchorStx : Syntax := .missing
  deriving Inhabited

def DeclReport.isWarning (r : DeclReport) : Bool :=
  r.severity == .warning

def DeclReport.lineCount (r : DeclReport) : Nat :=
  if r.endLine >= r.line && r.line > 0 then r.endLine - r.line + 1 else 1

/-- Sort decision points by highest impact first (`delta` desc, `depth` desc, `line` asc). -/
def DeclReport.topHotspots (r : DeclReport) (limit : Nat := 5) : Array DecisionPoint :=
  let sorted := r.decisionPoints.qsort fun a b =>
    if a.delta != b.delta then a.delta > b.delta
    else if a.depth != b.depth then a.depth > b.depth
    else a.line < b.line
  sorted.extract 0 (min limit sorted.size)

instance : ToJson DeclReport where
  toJson r := Json.mkObj [
    ("file", Json.str r.file),
    ("name", Json.str r.name),
    ("kind", toJson r.kind),
    ("severity", toJson r.severity),
    ("complexity", toJson r.complexity),
    ("effectiveComplexity", toJson r.effectiveComplexity),
    ("threshold", toJson r.threshold),
    ("maxDepth", toJson r.maxDepth),
    ("maxDepthThreshold", toJson r.maxDepthThreshold),
    ("line", toJson r.line),
    ("col", toJson r.col),
    ("endLine", toJson r.endLine),
    ("lineCount", toJson r.lineCount),
    ("pattern", toJson r.pattern),
    ("triggers", toJson r.triggers),
    ("breakdown", toJson r.breakdown),
    ("hotspots", toJson (r.topHotspots 8)),
    ("suggestions", toJson r.suggestions),
    ("suppress", Json.mkObj [
      ("raiseThreshold", Json.str s!"set_option linter.cyclo.{if r.kind.isProof then "proofThreshold" else "threshold"} {r.effectiveComplexity} in"),
      ("disable", Json.str "set_option linter.cyclo false in")
    ])
  ]

/-- Aggregated report across one or more scanned files. -/
structure ScanSummary where
  filesScanned : Nat
  declarationsAnalyzed : Nat
  warningsCount : Nat
  maxComplexity : Nat
  parseErrors : Array String
  reports : Array DeclReport
  deriving Inhabited

instance : ToJson ScanSummary where
  toJson s := Json.mkObj [
    ("schemaVersion", Json.str "1.0"),
    ("tool", Json.str "lean-cyclo"),
    ("filesScanned", toJson s.filesScanned),
    ("declarationsAnalyzed", toJson s.declarationsAnalyzed),
    ("warningsCount", toJson s.warningsCount),
    ("maxComplexity", toJson s.maxComplexity),
    ("parseErrors", toJson s.parseErrors),
    ("reports", toJson s.reports)
  ]

end Cyclo
