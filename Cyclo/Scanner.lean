import Lean
import Cyclo.Config
import Cyclo.Metrics
import Cyclo.Analyzer

/-!
# Fast File & Directory Scanner (Real Lean 4 Parser)

Parses `.lean` files using Lean 4's built-in `Parser.parseHeader` and
`Parser.parseCommand` without full elaboration, while tracking file-local
`namespace` / `end` scopes and `set_option linter.cyclo...` overrides (both
persistent and `... in <cmd>` scoped) so CLI results stay consistent with the
live Lean 4 command linter.
-/

namespace Cyclo

open Lean

/-- Mutable scanning state maintained across top-level commands in a single file. -/
private structure FileScanState where
  enabled : Bool := true
  cfg : Config
  nsStack : Array String := #[]
  reports : Array DeclReport := #[]
  parseErrors : Array String := #[]
  deriving Inhabited

private def currentNsPrefix (stack : Array String) : String :=
  if stack.isEmpty then "" else String.intercalate "." stack.toList

/-- Process a single parsed command, handling `in`-scoped options, `set_option`, `namespace`, and `end`. -/
private partial def processCommand (file : String) (fileMap : FileMap)
    (st : FileScanState) (cmdStx : Syntax) : FileScanState :=
  let k := cmdStx.getKind
  if k == `Lean.Parser.Command.in then
    let (localEnabled, localCfg, innerCmd) := unwrapInCommand st.enabled st.cfg cmdStx
    if localEnabled then
      let scopedSt := { st with enabled := true, cfg := localCfg, reports := #[] }
      let after := processCommand file fileMap scopedSt innerCmd
      { st with reports := st.reports ++ after.reports }
    else
      st
  else if k == `Lean.Parser.Command.set_option then
    let (en, c) := applySetOptionStx st.enabled st.cfg cmdStx
    { st with enabled := en, cfg := c }
  else if k == `Lean.Parser.Command.namespace then
    match cmdStx.getArgs[1]?.bind syntaxAtomOrIdent with
    | some ns => { st with nsStack := st.nsStack.push ns }
    | none => st
  else if k == `Lean.Parser.Command.end then
    if st.nsStack.isEmpty then st else { st with nsStack := st.nsStack.pop }
  else if st.enabled then
    let newReports := analyzeCommand st.cfg file fileMap cmdStx (currentNsPrefix st.nsStack)
    { st with reports := st.reports ++ newReports }
  else
    st

/-- Parse and analyze a single Lean source string using Lean's real parser. -/
def scanSource (env : Environment) (cfg : Config) (file : String) (source : String) :
    IO (Array DeclReport × Array String) := do
  let inputCtx := Parser.mkInputContext source file
  let (headerStx, parserState, messages) ← Parser.parseHeader inputCtx
  let _ := headerStx
  let mut st : FileScanState := { cfg }
  if messages.hasErrors then
    for m in messages.toList do
      if m.severity == .error then
        st := { st with parseErrors := st.parseErrors.push s!"{file}:{m.pos.line}:{m.pos.column}: header parse error" }
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let mut pstate := parserState
  let mut msgs := messages
  -- Guard against any pathological parser stall by capping iterations at source length + 1.
  let maxIters := source.length + 1
  for _ in [:maxIters] do
    let prevPos := pstate.pos
    let (cmdStx, nextPState, nextMsgs) := Parser.parseCommand inputCtx pmctx pstate msgs
    pstate := nextPState
    msgs := nextMsgs
    if Parser.isTerminalCommand cmdStx then
      break
    st := processCommand file inputCtx.fileMap st cmdStx
    if pstate.pos == prevPos then
      break
  return (st.reports, st.parseErrors)

/-- Parse and analyze a `.lean` file on disk. -/
def scanFile (env : Environment) (cfg : Config) (path : System.FilePath) :
    IO (Array DeclReport × Array String) := do
  let source ← IO.FS.readFile path
  scanSource env cfg path.toString source

private def ignoredDirNames : Array String :=
  #[".git", ".lake", "build", "node_modules", ".jj", "target"]

/-- Recursively discover `.lean` files under a file or directory path. -/
partial def collectLeanFiles (path : System.FilePath) : IO (Array System.FilePath) := do
  if !(← path.pathExists) then
    return #[]
  if ← path.isDir then
    let mut acc : Array System.FilePath := #[]
    let entries ← path.readDir
    let sortedEntries := entries.qsort (·.fileName < ·.fileName)
    for entry in sortedEntries do
      let name := entry.fileName
      if ignoredDirNames.contains name then
        continue
      if ← entry.path.isDir then
        let sub ← collectLeanFiles entry.path
        acc := acc ++ sub
      else if entry.path.extension == some "lean" then
        acc := acc.push entry.path
    return acc
  else if path.extension == some "lean" then
    return #[path]
  else
    return #[]

private unsafe def mkParserEnvironmentUnsafe : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  importModules #[{ module := `Init }] {} (loadExts := true)

/-- Build a Lean `Environment` with `Init` parser extensions loaded so all standard notations
    (`if/then/else`, `if let`, `&&`, `||`, `<|>`, `by_cases`, etc.) parse identically to `lean`. -/
@[implemented_by mkParserEnvironmentUnsafe]
def mkParserEnvironment : IO Environment := do
  initSearchPath (← findSysroot)
  importModules #[{ module := `Init }] {}

/-- Scan a list of file/directory paths and return an aggregated `ScanSummary`. -/
def scanPaths (cfg : Config) (paths : Array System.FilePath) : IO ScanSummary := do
  let env ← mkParserEnvironment
  let mut files : Array System.FilePath := #[]
  for p in paths do
    let found ← collectLeanFiles p
    files := files ++ found
  let mut allReports : Array DeclReport := #[]
  let mut allErrors : Array String := #[]
  for f in files do
    let (reps, errs) ← scanFile env cfg f
    allReports := allReports ++ reps
    allErrors := allErrors ++ errs
  let warningsCount := allReports.foldl (init := 0) fun acc r =>
    if r.isWarning then acc + 1 else acc
  let maxComplexity := allReports.foldl (init := 0) fun acc r =>
    max acc r.complexity
  return {
    filesScanned := files.size
    declarationsAnalyzed := allReports.size
    warningsCount
    maxComplexity
    parseErrors := allErrors
    reports := allReports
  }

end Cyclo
