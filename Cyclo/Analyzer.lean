import Lean
import Cyclo.Config
import Cyclo.Metrics

/-!
# Lean 4 Syntax-Tree Cyclomatic Complexity Analyzer

Computes exact McCabe cyclomatic complexity, branch nesting depth, category
breakdowns, structural complexity patterns, and actionable refactoring plans
directly from Lean 4 `Syntax` trees.

Key design choices:
- **Body-only analysis**: Type signatures (`declSig` / `optDeclSig`) are skipped
  so `if`/`match` appearing in theorem statements or dependent types do not
  inflate a declaration's complexity.
- **Flat `else if` chains**: Chained `else if` branches add `+1` to cyclomatic
  complexity without artificially inflating nesting depth.
- **`where` helpers as separate units**: Local `where` declarations are analyzed
  as `<parent>.<helper>` so extracting a `where` helper immediately reduces the
  parent's complexity.
- **1-arm destructuring `match` = +0**: Single-arm matches (`match x with | ⟨a, b⟩ => ...`)
  destructure without branching, matching strict McCabe theory (`k - 1 = 0`).
-/

namespace Cyclo

open Lean

/-- Accumulated state during a single declaration body walk. -/
private structure WalkState where
  points : Array DecisionPoint := #[]
  maxDepth : Nat := 0
  deriving Inhabited

private abbrev WalkM := ReaderT FileMap (StateM WalkState)

private def spanOf (fileMap : FileMap) (stx : Syntax) : Nat × Nat × Nat :=
  match stx.getRange? with
  | some range =>
    let startPos := fileMap.toPosition range.start
    let endPos := fileMap.toPosition range.stop
    (startPos.line, startPos.column + 1, endPos.line)
  | none => (0, 0, 0)

private def recordPoint (stx : Syntax) (kind : BranchKind) (delta depth : Nat) : WalkM Unit := do
  if delta == 0 then return
  let fm ← read
  let (line, col, endLine) := spanOf fm stx
  modify fun st => {
    points := st.points.push { kind, delta, depth, line, col, endLine }
    maxDepth := max st.maxDepth depth
  }

/-- Count `matchAlt` / `matchExprAlt` / `matchExprElseAlt` nodes inside a `matchAlts` subtree. -/
private def collectMatchAlts (stx : Syntax) : Array Syntax :=
  if stx.getKind == `Lean.Parser.Term.matchAlts || stx.getKind == `Lean.Parser.Term.matchExprAlts then
    stx.getArgs.foldl (init := #[]) fun acc arg =>
      if arg.getKind == `null then
        arg.getArgs.foldl (init := acc) fun acc2 item =>
          if isAlt item then acc2.push item else acc2
      else if isAlt arg then
        acc.push arg
      else
        acc
  else
    #[]
where
  isAlt (s : Syntax) : Bool :=
    let k := s.getKind
    k == `Lean.Parser.Term.matchAlt ||
    k == `Lean.Parser.Term.matchExprAlt ||
    k == `Lean.Parser.Term.matchExprElseAlt

/-- Collect `inductionAlt` nodes from an `inductionAlts` node if present inside `args`. -/
private def findInductionAlts (args : Array Syntax) : Option (Array Syntax) :=
  args.findSome? fun arg =>
    if arg.getKind == `Lean.Parser.Tactic.inductionAlts then
      some <| collectFromAlts arg
    else if arg.getKind == `null then
      arg.getArgs.findSome? fun sub =>
        if sub.getKind == `Lean.Parser.Tactic.inductionAlts then some (collectFromAlts sub) else none
    else
      none
where
  collectFromAlts (altsNode : Syntax) : Array Syntax :=
    altsNode.getArgs.foldl (init := #[]) fun acc a =>
      if a.getKind == `Lean.Parser.Tactic.inductionAlt then acc.push a
      else if a.getKind == `null then
        a.getArgs.foldl (init := acc) fun acc2 b =>
          if b.getKind == `Lean.Parser.Tactic.inductionAlt then acc2.push b else acc2
      else acc

/-- Detect whether a `doPatDecl` contains an `| fallback` branch. -/
private def hasDoPatFallback (stx : Syntax) : Bool :=
  stx.getArgs.any fun arg =>
    match arg with
    | .atom _ "|" => true
    | .node _ `null subArgs => subArgs.any fun s =>
        match s with
        | .atom _ "|" => true
        | .node _ `Lean.Parser.Term.doSeqIndent _ => true
        | .node _ `Lean.Parser.Term.doSeqBracketed _ => true
        | _ => false
    | _ => false

/-- Check if a syntax node kind is an `if`-like term node (for flat `else if` detection). -/
private def isTermIfKind (k : Name) : Bool :=
  k == `termIfThenElse || k == `termDepIfThenElse || k == `termIfLet

/-- Check if a tactic syntax kind represents `by_cases` (core or Mathlib). -/
private def isByCasesKind (k : Name) : Bool :=
  let s := k.toStringWithSep "." (escape := false)
  k == `«tacticBy_cases_:_» || k == `Lean.Parser.Tactic.byCases ||
    s.endsWith ".byCases" || s.endsWith ".by_cases" || s.startsWith "tacticBy_cases"

/-- Check if a tactic syntax kind is a Mathlib/custom case-splitting tactic. -/
private def isExtraSplitTactic (k : Name) : Bool :=
  let s := k.toStringWithSep "." (escape := false)
  s.endsWith ".rcases" || s.endsWith ".splitIfs" || s.endsWith ".intervalCases" ||
    s.endsWith ".finCases"

/-- Syntax node kinds skipped during body traversal (signatures & separate `where` helpers). -/
private def isSkippedBodyNode (k : Name) : Bool :=
  k == `Lean.Parser.Term.whereDecls ||
  k == `Lean.Parser.Term.typeSpec ||
  k == `Lean.Parser.Command.declSig ||
  k == `Lean.Parser.Command.optDeclSig

private def simpleBranchTable : Array (Name × BranchKind × Bool) := #[
  (`Lean.Parser.Term.doUnless, .doUnless, true),
  (`Lean.Parser.Term.termUnless, .doUnless, true),
  (`Lean.Parser.Term.doFor, .doFor, true),
  (`Lean.Parser.Term.termFor, .doFor, true),
  (`Lean.Parser.Term.doWhile, .doWhile, true),
  (`Lean.Parser.Term.doRepeat, .doRepeat, true),
  (`Lean.Parser.Term.doRepeatUntil, .doRepeat, true),
  (`Lean.Parser.Term.doLetElse, .doLetElse, true),
  (`«term_&&_», .boolAnd, false),
  (`«term_||_», .boolOr, false),
  (`«term_<|>_», .orElse, false),
  (`Lean.Parser.Tactic.split, .tacticSplit, true),
  (`Lean.Parser.Tactic.tacticTry_, .tacticTry, true),
  (`Lean.Parser.Tactic.tacticRepeat_, .tacticRepeat, true),
  (`Lean.Parser.Tactic.tacticOrelse, .tacticOrElse, true),
  (`«tactic_<|>_», .tacticOrElse, true)
]

/-- Map a simple single-decision syntax node kind to its `BranchKind` and whether it increments depth. -/
private def simpleBranchKind? (k : Name) : Option (BranchKind × Bool) :=
  (simpleBranchTable.find? (·.1 == k)).map fun (_, bk, nest) => (bk, nest)

private def isTermMatchKind (k : Name) : Bool :=
  k == `Lean.Parser.Term.match || k == `Lean.Parser.Term.doMatch ||
  k == `Lean.Parser.Term.matchExpr || k == `Lean.Parser.Term.doMatchExpr

private def countFirstBranches (args : Array Syntax) : Nat :=
  args.foldl (init := 0) fun n a =>
    if a.getKind == `null then n + a.getArgs.size
    else if a.getKind == `group then n + 1
    else n

mutual
  /-- Walk an array of child syntax nodes at `depth`. -/
  private partial def walkChildren (args : Array Syntax) (depth : Nat) : WalkM Unit := do
    for arg in args do
      walkSyntax arg depth

  /-- Analyze `matchAlts` arms, recording `delta` (either `arms - 1` or `arms` for catch-match)
      and recursing into each arm's RHS at `depth + 1`. -/
  private partial def walkMatchAltsNode (anchor : Syntax) (altsNode : Syntax)
      (mkKind : Nat → BranchKind) (countAllArms : Bool) (depth : Nat) : WalkM Unit := do
    let alts := collectMatchAlts altsNode
    let k := alts.size
    let delta := if countAllArms then max 1 k else if k > 1 then k - 1 else 0
    let branchDepth := depth + 1
    if delta > 0 then
      recordPoint anchor (mkKind k) delta branchDepth
    let nextDepth := if delta > 0 then branchDepth else depth
    for alt in alts do
      let altArgs := alt.getArgs
      if h : altArgs.size > 0 then
        walkSyntax altArgs[altArgs.size - 1] nextDepth

  /-- Walk a term-level `if` / `if h :` / `if let` without inflating depth on `else if`. -/
  private partial def walkTermIf (stx : Syntax) (kind : BranchKind) (depth : Nat)
      (isElseIf : Bool := false) : WalkM Unit := do
    let branchDepth := depth + 1
    let recordedKind := if isElseIf then .elseIfBranch else kind
    recordPoint stx recordedKind 1 branchDepth
    let args := stx.getArgs
    for i in [:args.size] do
      let arg := args[i]!
      if i == args.size - 1 && isTermIfKind arg.getKind then
        walkTermIf arg (termIfKind arg.getKind) depth (isElseIf := true)
      else if i == args.size - 1 || (args.size >= 4 && i == args.size - 3) then
        walkSyntax arg branchDepth
      else
        walkSyntax arg depth

  private partial def termIfKind (k : Name) : BranchKind :=
    if k == `termDepIfThenElse then .depIfExpr
    else if k == `termIfLet then .ifLetExpr
    else .ifExpr

  /-- Walk a `doIf` node: main `if`, optional `else if` chain (same depth), and optional `else`. -/
  private partial def walkDoIf (stx : Syntax) (depth : Nat) : WalkM Unit := do
    let branchDepth := depth + 1
    recordPoint stx .doIf 1 branchDepth
    let args := stx.getArgs
    if h1 : 1 < args.size then walkSyntax args[1] depth
    if h3 : 3 < args.size then walkSyntax args[3] branchDepth
    if h4 : 4 < args.size then
      for grp in args[4].getArgs do
        recordPoint grp .elseIfBranch 1 branchDepth
        let gArgs := grp.getArgs
        for j in [:gArgs.size] do
          let ga := gArgs[j]!
          let d := if j == gArgs.size - 1 then branchDepth else depth
          walkSyntax ga d
    if h5 : 5 < args.size then walkSyntax args[5] branchDepth

  /-- Walk `doTry` / `termTry`, handling `doCatch`, `doCatchMatch`, and `doFinally`. -/
  private partial def walkTry (stx : Syntax) (depth : Nat) : WalkM Unit := do
    for arg in stx.getArgs do
      walkTryPart arg depth

  private partial def walkTryPart (arg : Syntax) (depth : Nat) : WalkM Unit := do
    let k := arg.getKind
    if k == `null then
      for sub in arg.getArgs do
        walkTryPart sub depth
    else if k == `Lean.Parser.Term.doCatch then
      recordPoint arg .tryCatch 1 (depth + 1)
      walkChildren arg.getArgs (depth + 1)
    else if k == `Lean.Parser.Term.doCatchMatch then
      let handled ← arg.getArgs.anyM fun sub => do
        if sub.getKind == `Lean.Parser.Term.matchAlts then
          walkMatchAltsNode arg sub .tryCatchMatch true depth
          pure true
        else
          pure false
      if !handled then
        recordPoint arg .tryCatch 1 (depth + 1)
        walkChildren arg.getArgs (depth + 1)
    else
      walkSyntax arg depth

  /-- Walk `cases` or `induction` tactic, respecting explicit `with | ...` alternatives. -/
  private partial def walkCasesOrInduction (stx : Syntax) (isInduction : Bool) (depth : Nat) : WalkM Unit := do
    let args := stx.getArgs
    let mkKind := if isInduction then BranchKind.tacticInduction else BranchKind.tacticCases
    match findInductionAlts args with
    | some alts =>
      let k := alts.size
      let delta := if k > 1 then k - 1 else 0
      if delta > 0 then
        recordPoint stx (mkKind k) delta (depth + 1)
      let nextDepth := if delta > 0 then depth + 1 else depth
      for alt in alts do
        walkChildren alt.getArgs nextDepth
    | none =>
      recordPoint stx (mkKind 0) 1 (depth + 1)
      walkChildren args (depth + 1)

  /-- Walk a `match` / `doMatch` / `matchExpr` / `doMatchExpr` / `Tactic.match` node. -/
  private partial def walkMatchNode (stx : Syntax) (isTactic : Bool) (depth : Nat) : WalkM Unit := do
    let mkKind := if isTactic then BranchKind.tacticMatch else BranchKind.matchArms
    for arg in stx.getArgs do
      let ak := arg.getKind
      if ak == `Lean.Parser.Term.matchAlts || ak == `Lean.Parser.Term.matchExprAlts then
        walkMatchAltsNode stx arg mkKind false depth
      else
        walkSyntax arg depth

  /-- Walk a `fun` node (handles pattern-matching lambdas `fun | a => ... | b => ...`). -/
  private partial def walkFunNode (stx : Syntax) (args : Array Syntax) (depth : Nat) : WalkM Unit := do
    for arg in args do
      if arg.getKind == `Lean.Parser.Term.matchAlts then
        walkMatchAltsNode stx arg .matchArms false depth
      else
        walkSyntax arg depth

  /-- Handle specialized tactic control-flow nodes; returns `true` if handled. -/
  private partial def walkSpecialTactic? (stx : Syntax) (k : Name) (args : Array Syntax)
      (depth : Nat) : WalkM Bool := do
    if k == `Lean.Parser.Tactic.match then
      walkMatchNode stx true depth; return true
    else if k == `Lean.Parser.Tactic.cases then
      walkCasesOrInduction stx false depth; return true
    else if k == `Lean.Parser.Tactic.induction then
      walkCasesOrInduction stx true depth; return true
    else if k == `Lean.Parser.Tactic.first then
      let branches := countFirstBranches args
      let delta := if branches > 1 then branches - 1 else 1
      recordPoint stx (.tacticFirst (max 1 branches)) delta (depth + 1)
      walkChildren args (depth + 1)
      return true
    else if isByCasesKind k || isExtraSplitTactic k then
      recordPoint stx .tacticByCases 1 (depth + 1)
      walkChildren args (depth + 1)
      return true
    else
      return false

  /-- Handle specialized term/do control-flow nodes; returns `true` if handled. -/
  private partial def walkSpecialTerm? (stx : Syntax) (k : Name) (args : Array Syntax)
      (depth : Nat) : WalkM Bool := do
    if isTermIfKind k then
      walkTermIf stx (termIfKind k) depth; return true
    else if k == `Lean.Parser.Term.doIf then
      walkDoIf stx depth; return true
    else if isTermMatchKind k then
      walkMatchNode stx false depth; return true
    else if k == `Lean.Parser.Term.fun then
      walkFunNode stx args depth; return true
    else if k == `Lean.Parser.Term.doTry || k == `Lean.Parser.Term.termTry then
      walkTry stx depth; return true
    else if k == `Lean.Parser.Term.doPatDecl && hasDoPatFallback stx then
      recordPoint stx .doLetElse 1 (depth + 1)
      walkChildren args (depth + 1)
      return true
    else
      return false

  /-- Main recursive syntax walker for a single declaration body. -/
  private partial def walkSyntax (stx : Syntax) (depth : Nat) : WalkM Unit := do
    match stx with
    | .node _ k args =>
      if isSkippedBodyNode k then
        return
      if let some (bkind, nest) := simpleBranchKind? k then
        let recDepth := if nest then depth + 1 else max 1 depth
        let childDepth := if nest then depth + 1 else depth
        recordPoint stx bkind 1 recDepth
        walkChildren args childDepth
        return
      if ← walkSpecialTerm? stx k args depth then return
      if ← walkSpecialTactic? stx k args depth then return
      walkChildren args depth
    | _ => pure ()
end

/-- Compute per-category delta totals from an array of decision points. -/
private def computeBreakdown (points : Array DecisionPoint) : CategoryBreakdown :=
  points.foldl (init := {}) fun acc dp =>
    match dp.kind.category with
    | .term => { acc with term := acc.term + dp.delta }
    | .doControl => { acc with doControl := acc.doControl + dp.delta }
    | .boolean => { acc with boolean := acc.boolean + dp.delta }
    | .errorHandling => { acc with errorHandling := acc.errorHandling + dp.delta }
    | .tactic => { acc with tactic := acc.tactic + dp.delta }

/-- Check if a decision point is a top-level flat match or equation table. -/
private def isFlatTopMatch (dp : DecisionPoint) : Bool :=
  dp.depth <= 1 &&
  match dp.kind with
  | .matchArms _ | .equationAlts _ => true
  | _ => false

private def maxTopMatchDelta (points : Array DecisionPoint) : Nat :=
  points.foldl (init := 0) fun acc dp =>
    if isFlatTopMatch dp then max acc dp.delta else acc

private def shareAtLeast (part total tenths : Nat) : Bool :=
  part * 10 >= total * tenths

/-- Classify the dominant complexity archetype of a declaration. -/
private def classifyPattern (kind : DeclKind) (points : Array DecisionPoint)
    (breakdown : CategoryBreakdown) (maxDepth : Nat) : ComplexityPattern :=
  let total := points.foldl (init := 0) fun acc dp => acc + dp.delta
  if total == 0 then
    .mixedBranching
  else if kind.isProof && shareAtLeast breakdown.tactic total 5 then
    .tacticExplosion
  else if maxDepth <= 2 && shareAtLeast (maxTopMatchDelta points) total 6 then
    .flatDispatch
  else if maxDepth >= 4 then
    .deepNesting
  else if shareAtLeast breakdown.boolean total 4 then
    .booleanSoup
  else if shareAtLeast breakdown.errorHandling total 4 then
    .errorHandlingHeavy
  else if shareAtLeast breakdown.doControl total 5 then
    .imperativeLoopNest
  else
    .mixedBranching

/-- Compute effective complexity after applying optional `flatMatchDiscount`. -/
private def computeEffectiveComplexity (cfg : Config) (rawComplexity : Nat)
    (pattern : ComplexityPattern) (points : Array DecisionPoint) : Nat :=
  if !cfg.flatMatchDiscount || pattern != .flatDispatch then
    rawComplexity
  else
    let discount := points.foldl (init := 0) fun acc dp =>
      if isFlatTopMatch dp && dp.delta > 1 then acc + (dp.delta - 1) else acc
    rawComplexity - discount

/-- Format a compact line range hint such as `L42-L60` or `L42`. -/
private def fmtSpan (dp : DecisionPoint) : String :=
  if dp.line == 0 then "body"
  else if dp.endLine > dp.line then s!"L{dp.line}-L{dp.endLine}"
  else s!"L{dp.line}"

private def primaryHotspot? (points : Array DecisionPoint) : Option DecisionPoint :=
  let sorted := points.qsort fun a b =>
    if a.delta != b.delta then a.delta > b.delta
    else if a.depth != b.depth then a.depth > b.depth
    else a.line < b.line
  sorted[0]?

private def deepestPoint? (points : Array DecisionPoint) : Option DecisionPoint :=
  points.foldl (init := none) fun best dp =>
    match best with
    | none => some dp
    | some b => if dp.depth > b.depth then some dp else some b

private def optSuggestion (dp? : Option DecisionPoint) (mk : DecisionPoint → RefactorSuggestion) :
    Array RefactorSuggestion :=
  match dp? with
  | some dp => #[mk dp]
  | none => #[]

private def primarySuggestions (pattern : ComplexityPattern) (top? deepest? : Option DecisionPoint)
    (breakdown : CategoryBreakdown) (maxDepth : Nat) : Array RefactorSuggestion :=
  match pattern with
  | .flatDispatch =>
    optSuggestion top? (fun top => {
      id := "split-dispatch-by-domain"
      action := s!"Group arms of {top.kind.label} at {fmtSpan top} into domain-specific `where` helpers or a lookup table."
      impact := s!"Keeps top-level dispatch flat while moving per-case logic out of the main body (currently +{top.delta} branches)."
    }) ++ #[{
      id := "document-intentional-dispatch"
      action := "If exhaustive enum dispatch is intentional, raise this declaration's local budget with `set_option linter.cyclo.threshold <N> in` or enable `linter.cyclo.flatMatchDiscount`."
      impact := "Avoids fighting legitimate AST/opcode evaluators."
    }]
  | .deepNesting =>
    optSuggestion deepest? (fun deep => {
      id := "extract-deep-branch"
      action := s!"Extract the nested `{deep.kind.label}` block at {fmtSpan deep} (depth {deep.depth}) into a named `where` or `private def` helper."
      impact := s!"Flattens nesting from depth {maxDepth} and immediately credits the extracted branches to the helper."
    }) ++ #[{
      id := "invert-guards"
      action := "Replace nested `if` / `if let` checks with early-return guard clauses (`if !cond then return ...` or `let some x := e | return ...`)."
      impact := "Eliminates indentation layers and isolates failure exits at the top of the block."
    }]
  | .booleanSoup =>
    optSuggestion top? (fun top => {
      id := "extract-named-predicates"
      action := s!"Extract compound boolean conditions around {fmtSpan top} into small named predicates (`private def isValid... : Bool`)."
      impact := s!"Moves {breakdown.boolean} boolean short-circuit branches into self-documenting, testable units."
    }) ++ #[{
      id := "use-pattern-matching"
      action := "Replace multi-clause `&&`/`||` chains checking structure fields with a single pattern `match`."
      impact := "Makes mutually exclusive cases explicit to Lean's exhaustiveness checker."
    }]
  | .imperativeLoopNest =>
    optSuggestion top? fun top => {
      id := "extract-loop-step"
      action := s!"Extract the loop body around {fmtSpan top} into a pure step helper `step state item` or use `Array.filterMap`/`foldl`."
      impact := "Decouples iteration control from per-element branching."
    }
  | .errorHandlingHeavy =>
    optSuggestion top? fun top => {
      id := "monadic-error-pipeline"
      action := s!"Lift `try/catch` and `let ... | fallback` branches around {fmtSpan top} into an `Except` / `OptionT` helper pipeline."
      impact := s!"Centralizes {breakdown.errorHandling} error-handling branches at one boundary."
    }
  | .tacticExplosion =>
    optSuggestion top? (fun top => {
      id := "extract-sublemmas"
      action := s!"Extract the heaviest case branch at {fmtSpan top} (`{top.kind.label}`) into a standalone helper `private lemma`/`theorem`."
      impact := "Shortens proof search context, speeds up elaboration, and makes tactic goals reusable."
    }) ++ #[{
      id := "collapse-case-splits"
      action := "Where branches close similarly, replace manual `cases`/`by_cases` trees with `simp`/`omega`/`grind` or `<;>` combinators."
      impact := "Reduces explicit proof-tree branching."
    }]
  | .mixedBranching =>
    optSuggestion top? fun top => {
      id := "extract-hotspot-where"
      action := s!"Extract `{top.kind.label}` at {fmtSpan top} (+{top.delta} CC) into a `where` helper function."
      impact := "Separates distinct decision phases into focused units with independent complexity budgets."
    }

private def secondarySuggestions (kind : DeclKind) (pattern : ComplexityPattern)
    (breakdown : CategoryBreakdown) : Array RefactorSuggestion :=
  let boolSug :=
    if breakdown.boolean >= 3 && pattern != .booleanSoup then #[{
      id := "extract-predicates"
      action := s!"Pull {breakdown.boolean} boolean (`&&`/`||`/`<|>`) branches into named predicate helpers."
      impact := "Simplifies branch conditions and clarifies invariants."
    }] else #[]
  let doSug :=
    if breakdown.doControl >= 3 && pattern != .imperativeLoopNest && !kind.isProof then #[{
      id := "split-do-phases"
      action := "Split imperative `do` logic into pure decision helpers plus a thin effectful shell."
      impact := "Improves testability and shrinks imperative control flow."
    }] else #[]
  boolSug ++ doSug

/-- Generate tailored, concrete Lean 4 refactoring actions from the actual hotspots. -/
private def buildSuggestions (kind : DeclKind) (pattern : ComplexityPattern)
    (points : Array DecisionPoint) (breakdown : CategoryBreakdown) (maxDepth : Nat) :
    Array RefactorSuggestion :=
  primarySuggestions pattern (primaryHotspot? points) (deepestPoint? points) breakdown maxDepth ++
    secondarySuggestions kind pattern breakdown

/-- Extract a readable identifier from a `declId` or `letId` syntax node. -/
private partial def extractIdentName (stx : Syntax) : Option String :=
  match stx with
  | .ident _ rawVal _ _ => some rawVal.toString
  | .node _ `Lean.Parser.Command.declId args =>
    if h : 0 < args.size then extractIdentName args[0] else none
  | .node _ `Lean.Parser.Term.letId args =>
    if h : 0 < args.size then extractIdentName args[0] else none
  | .node _ _ args => args.findSome? extractIdentName
  | _ => none

/-- Collect direct `letRecDecl` sub-declarations from any `whereDecls` node inside `stx`. -/
private partial def collectWhereDecls (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ `Lean.Parser.Term.whereDecls args =>
    args.foldl (init := #[]) fun acc a =>
      if a.getKind == `Lean.Parser.Term.letRecDecl then acc.push a
      else if a.getKind == `null then
        a.getArgs.foldl (init := acc) fun acc2 b =>
          if b.getKind == `Lean.Parser.Term.letRecDecl then acc2.push b else acc2
      else acc
  | .node _ _ args =>
    args.foldl (init := #[]) fun acc a => acc ++ collectWhereDecls a
  | _ => #[]

/-- Build a finalized `DeclReport` from raw walk state. -/
private def finalizeReport (cfg : Config) (file : String) (name : String) (kind : DeclKind)
    (anchorStx : Syntax) (spanStx : Syntax) (fileMap : FileMap) (st : WalkState) : DeclReport :=
  let totalDelta := st.points.foldl (init := 0) fun acc dp => acc + dp.delta
  let rawCC := 1 + totalDelta
  let breakdown := computeBreakdown st.points
  let pattern := classifyPattern kind st.points breakdown st.maxDepth
  let effectiveCC := computeEffectiveComplexity cfg rawCC pattern st.points
  let threshold := if kind.isProof then cfg.proofThreshold else cfg.threshold
  let (line, col, endLine) := spanOf fileMap spanStx
  let triggers := Id.run do
    let mut ts : Array String := #[]
    if effectiveCC > threshold then
      ts := ts.push s!"complexity {effectiveCC} > threshold {threshold}"
    if cfg.maxDepth > 0 && st.maxDepth > cfg.maxDepth then
      ts := ts.push s!"nesting depth {st.maxDepth} > maxDepth {cfg.maxDepth}"
    return ts
  let severity := if triggers.isEmpty then .ok else .warning
  let suggestions :=
    if severity == .warning || cfg.reportAll then
      buildSuggestions kind pattern st.points breakdown st.maxDepth
    else
      #[]
  {
    file, name, kind
    complexity := rawCC
    effectiveComplexity := effectiveCC
    threshold
    maxDepth := st.maxDepth
    maxDepthThreshold := cfg.maxDepth
    line, col, endLine
    pattern, severity, triggers, breakdown
    decisionPoints := st.points
    suggestions
    anchorStx
  }

private def walkMatchAltsWhereDecls (anchor : Syntax) (node : Syntax) : WalkM Unit := do
  for sub in node.getArgs do
    if sub.getKind == `Lean.Parser.Term.matchAlts then
      walkMatchAltsNode anchor sub .equationAlts false 0
    else if sub.getKind != `Lean.Parser.Term.whereDecls then
      walkSyntax sub 0

/-- Analyze a declaration value node (`declValSimple`, `declValEqns`, `whereStructInst`, etc.). -/
private def walkDeclVal (valStx : Syntax) : WalkM Unit := do
  match valStx with
  | .node _ `Lean.Parser.Command.declValEqns args =>
    for arg in args do
      if arg.getKind == `Lean.Parser.Term.matchAltsWhereDecls then
        walkMatchAltsWhereDecls valStx arg
      else
        walkSyntax arg 0
  | .node _ `Lean.Parser.Command.declValSimple args =>
    for arg in args do
      if arg.getKind != `Lean.Parser.Term.whereDecls then
        walkSyntax arg 0
  | .node _ `Lean.Parser.Command.whereStructInst args =>
    walkChildren args 0
  | _ =>
    walkSyntax valStx 0

/-- Analyze a single `letRecDecl` inside a `where` clause. -/
private def analyzeWhereDecl (cfg : Config) (file : String) (parentName : String)
    (fileMap : FileMap) (letRecStx : Syntax) : Option DeclReport :=
  let helperName :=
    match letRecStx.getArgs.findSome? fun a =>
      if a.getKind == `Lean.Parser.Term.letDecl then extractIdentName a else none with
    | some n => s!"{parentName}.{n}"
    | none => s!"{parentName}.where"
  let bodyOpt := letRecStx.getArgs.findSome? fun a =>
    if a.getKind == `Lean.Parser.Term.letDecl then some a else none
  match bodyOpt with
  | none => none
  | some letDecl =>
    let ((), st) := (walkLetDeclBody letDecl).run fileMap |>.run {}
    some (finalizeReport cfg file helperName .whereHelper letRecStx letRecStx fileMap st)
where
  walkLetDeclBody (letDecl : Syntax) : WalkM Unit := do
    for arg in letDecl.getArgs do
      if arg.getKind == `Lean.Parser.Term.letIdDecl then
        let idArgs := arg.getArgs
        if h : idArgs.size > 0 then
          walkSyntax idArgs[idArgs.size - 1] 0
      else if arg.getKind == `Lean.Parser.Term.letEqnsDecl then
        for sub in arg.getArgs do
          if sub.getKind == `Lean.Parser.Term.matchAlts then
            walkMatchAltsNode arg sub .equationAlts false 0
      else
        walkSyntax arg 0

private def declKindOfSyntaxKind? : Name → Option DeclKind
  | `Lean.Parser.Command.definition => some .definition
  | `Lean.Parser.Command.abbrev => some .abbrevDecl
  | `Lean.Parser.Command.theorem => some .theoremDecl
  | `Lean.Parser.Command.instance => some .instanceDecl
  | `Lean.Parser.Command.opaque => some .opaqueDecl
  | `Lean.Parser.Command.example => some .exampleDecl
  | _ => none

private def isDeclValKind (k : Name) : Bool :=
  k == `Lean.Parser.Command.declValSimple ||
  k == `Lean.Parser.Command.declValEqns ||
  k == `Lean.Parser.Command.whereStructInst

/-- Extract the declaration kind, display name, anchor syntax, and value syntax from an inner decl node. -/
private def inspectInnerDecl (inner : Syntax) : Option (DeclKind × String × Syntax × Syntax) := do
  let declKind ← declKindOfSyntaxKind? inner.getKind
  let args := inner.getArgs
  let valStx ← args.findSome? fun a => if isDeclValKind a.getKind then some a else none
  let declId? := args.findSome? fun a =>
    if a.getKind == `Lean.Parser.Command.declId then some a else none
  let anchorStx := declId?.getD inner
  let rawName := (declId?.bind extractIdentName).getD s!"<{declKind}>"
  return (declKind, rawName, anchorStx, valStx)

/-- Extract an identifier, atom, or numeric literal from a syntax leaf. -/
def syntaxAtomOrIdent (stx : Syntax) : Option String :=
  match stx with
  | .ident _ rawVal _ _ => some rawVal.toString
  | .atom _ val => some val
  | .node _ `num #[.atom _ val] => some val
  | _ => none

private def applyBoolOption (enabled : Bool) (cfg : Config) (name : String) (v : Bool) :
    Option (Bool × Config) :=
  match name with
  | "linter.cyclo" => some (v, cfg)
  | "linter.cyclo.includeProofs" => some (enabled, { cfg with includeProofs := v })
  | "linter.cyclo.flatMatchDiscount" => some (enabled, { cfg with flatMatchDiscount := v })
  | "linter.cyclo.json" => some (enabled, { cfg with emitJson := v })
  | "linter.cyclo.reportAll" => some (enabled, { cfg with reportAll := v })
  | _ => none

private def applyNatOption (cfg : Config) (name : String) (n : Nat) : Option Config :=
  match name with
  | "linter.cyclo.threshold" => some { cfg with threshold := n }
  | "linter.cyclo.proofThreshold" => some { cfg with proofThreshold := n }
  | "linter.cyclo.maxDepth" => some { cfg with maxDepth := n }
  | _ => none

/-- Apply a `set_option <name> <val>` syntax node to `(enabled, cfg)`. -/
def applySetOptionStx (enabled : Bool) (cfg : Config) (cmdStx : Syntax) : Bool × Config :=
  let args := cmdStx.getArgs
  let optName? := args[1]?.bind syntaxAtomOrIdent
  -- `set_option` has `[atom("set_option"), ident, optArgs(null), val]` so take `args[3]?` or `args[2]?`.
  let optVal? := (args[3]?.orElse fun () => args[2]?).bind syntaxAtomOrIdent
  match optName?, optVal? with
  | some name, some val =>
    let norm := if name.startsWith "weak." then (name.drop 5).toString else name
    if let some res := applyBoolOption enabled cfg norm (val == "true") then
      res
    else if let some nextCfg := val.toNat?.bind (applyNatOption cfg norm) then
      (enabled, nextCfg)
    else
      (enabled, cfg)
  | _, _ => (enabled, cfg)

/-- Unwrap nested `... in <cmd>` wrappers, applying any local `set_option linter.cyclo.*` overrides. -/
partial def unwrapInCommand (enabled : Bool) (cfg : Config) (cmdStx : Syntax) :
    Bool × Config × Syntax :=
  if cmdStx.getKind == `Lean.Parser.Command.in then
    let args := cmdStx.getArgs
    if h : args.size >= 3 then
      let lhs := args[0]
      let rhs := args[2]
      let (nextEn, nextCfg) :=
        if lhs.getKind == `Lean.Parser.Command.set_option then
          applySetOptionStx enabled cfg lhs
        else
          (enabled, cfg)
      unwrapInCommand nextEn nextCfg rhs
    else
      (enabled, cfg, cmdStx)
  else
    (enabled, cfg, cmdStx)

private def qualifyName (nsPrefix rawName : String) : String :=
  if nsPrefix.isEmpty || rawName.startsWith "<" then rawName else s!"{nsPrefix}.{rawName}"

private def analyzeSingleDeclaration (cfg : Config) (file : String) (fileMap : FileMap)
    (stx : Syntax) (nsPrefix : String) : Array DeclReport :=
  let inner? := stx.getArgs.findSome? fun a =>
    if a.getKind != `Lean.Parser.Command.declModifiers then some a else none
  match inner?.bind inspectInnerDecl with
  | none => #[]
  | some (declKind, rawName, anchorStx, valStx) =>
    if declKind.isProof && !cfg.includeProofs then
      #[]
    else
      let fullName := qualifyName nsPrefix rawName
      let ((), walkSt) := (walkDeclVal valStx).run fileMap |>.run {}
      let mainReport := finalizeReport cfg file fullName declKind anchorStx stx fileMap walkSt
      let whereReports := (collectWhereDecls valStx).filterMap fun w =>
        analyzeWhereDecl cfg file fullName fileMap w
      #[mainReport] ++ whereReports

/-- Analyze a single top-level command `Syntax` (including `in`, `mutual`, and `where` helpers). -/
partial def analyzeCommand (cfg : Config) (file : String) (fileMap : FileMap)
    (cmdStx : Syntax) (nsPrefix : String := "") : Array DeclReport :=
  let (enabled, effCfg, innerCmd) := unwrapInCommand true cfg cmdStx
  if !enabled then
    #[]
  else if innerCmd.getKind == `Lean.Parser.Command.mutual then
    innerCmd.getArgs.foldl (init := #[]) fun acc arg =>
      if arg.getKind == `null then
        arg.getArgs.foldl (init := acc) fun acc2 sub =>
          acc2 ++ analyzeCommand effCfg file fileMap sub nsPrefix
      else if arg.getKind == `Lean.Parser.Command.declaration then
        acc ++ analyzeCommand effCfg file fileMap arg nsPrefix
      else
        acc
  else if innerCmd.getKind == `Lean.Parser.Command.declaration then
    analyzeSingleDeclaration effCfg file fileMap innerCmd nsPrefix
  else
    #[]

end Cyclo
