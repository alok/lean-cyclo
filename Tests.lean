import Lean
import Cyclo

/-!
# `lean-cyclo` Test Suite

1. Compile-time live linter checks using `#guard_msgs` to verify native Lean 4
   `Command.Linter` integration, local overrides, and info/warning behavior.
2. Runtime unit test suite (`lake test`) verifying exact McCabe counts, nesting
   depths, pattern diagnosis, `where`/`mutual` handling, tactic proofs, and JSON
   output across all Lean 4 control-flow constructs.
-/

-- ============================================================================
-- Section 1: Live Lean 4 Command Linter Verification
-- ============================================================================

namespace LiveLinterChecks

-- Clean declaration within threshold produces no diagnostic.
#guard_msgs in
def simpleAdd (x y : Nat) : Nat := x + y

-- Low-threshold override triggers a structured AI-first warning.
/--
warning: [cyclo] `LiveLinterChecks.branchy` (def) cyclomatic complexity = 4 (threshold: 2, max_depth: 1, pattern: mixed-branching)
Triggered: complexity 4 > threshold 2
Breakdown (+3 decision points): term:+3
Hotspots:
  1. L43:3  +1  if/then/else [depth 1]
  2. L44:8  +1  else if [depth 1]
  3. L45:8  +1  else if [depth 1]
Refactor options:
  - [extract-hotspot-where] Extract `if/then/else` at L43-L46 (+1 CC) into a `where` helper function.
    Impact: Separates distinct decision phases into focused units with independent complexity budgets.
Local override: `set_option linter.cyclo.threshold 4 in` or `set_option linter.cyclo false in`

Note: This linter can be disabled with `set_option linter.cyclo false`
-/
#guard_msgs in
set_option linter.cyclo.threshold 2 in
def branchy (x : Nat) : Nat :=
  if x == 0 then 1
  else if x == 1 then 2
  else if x == 2 then 3
  else 4

-- `set_option linter.cyclo false in` suppresses the linter locally.
#guard_msgs in
set_option linter.cyclo false in
set_option linter.cyclo.threshold 1 in
def intentionallySuppressed (x : Nat) : Nat :=
  if x == 0 then 1 else if x == 1 then 2 else 3

-- Raising `linter.cyclo.threshold` locally clears the warning.
#guard_msgs in
set_option linter.cyclo.threshold 4 in
def budgetedBranchy (x : Nat) : Nat :=
  if x == 0 then 1
  else if x == 1 then 2
  else if x == 2 then 3
  else 4

-- `reportAll` emits an info diagnostic even when within budget.
/--
info: [cyclo] `LiveLinterChecks.auditedFn` (def) CC=2/10, max_depth=1, pattern=mixed-branching, breakdown=[term:+1]
-/
#guard_msgs in
set_option linter.cyclo.reportAll true in
def auditedFn (b : Bool) : Nat := if b then 1 else 0

end LiveLinterChecks

-- ============================================================================
-- Section 2: Exhaustive Runtime Unit Tests (`lake test`)
-- ============================================================================

open Lean Cyclo

private def assertEq [BEq α] [ToString α] (label : String) (actual expected : α) : IO Unit := do
  if actual != expected then
    throw <| IO.userError s!"FAIL [{label}]: expected `{expected}`, got `{actual}`"

private def assertTrue (label : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw <| IO.userError s!"FAIL [{label}]: expected true"

private def scanOne (env : Environment) (src : String) (cfg : Config := {}) : IO DeclReport := do
  let (reps, errs) ← scanSource env cfg "<test>" src
  if !errs.isEmpty then
    throw <| IO.userError s!"Unexpected parse errors: {errs}"
  if h : reps.size > 0 then
    return reps[0]
  else
    throw <| IO.userError s!"Expected at least 1 DeclReport for:\n{src}"

private def testTermConstructs (env : Environment) : IO Unit := do
  -- Base simple def: CC = 1, depth = 0
  let r0 ← scanOne env "def f (x : Nat) : Nat := x + 1"
  assertEq "simple CC" r0.complexity 1
  assertEq "simple depth" r0.maxDepth 0
  assertEq "simple name" r0.name "f"

  -- Single if/then/else: CC = 2, depth = 1
  let r1 ← scanOne env "def f (x : Nat) : Nat := if x == 0 then 1 else 2"
  assertEq "if CC" r1.complexity 2
  assertEq "if depth" r1.maxDepth 1

  -- Flat else-if chain: CC = 4, depth = 1 (must NOT inflate nesting depth!)
  let r2 ← scanOne env
    "def f (x : Nat) : Nat :=\n  if x == 0 then 1\n  else if x == 1 then 2\n  else if x == 2 then 3\n  else 4"
  assertEq "else-if chain CC" r2.complexity 4
  assertEq "else-if chain depth" r2.maxDepth 1

  -- Dependent if + if let
  let r3 ← scanOne env "def f (x : Nat) : Nat := if h : x > 0 then x else 0"
  assertEq "dep if CC" r3.complexity 2
  let r4 ← scanOne env "def f (x : Option Nat) : Nat := if let some n := x then n else 0"
  assertEq "if let CC" r4.complexity 2

  -- 1-arm destructuring match = +0 (strict McCabe!)
  let r5 ← scanOne env "def f (p : Nat × Nat) : Nat := match p with | (a, b) => a + b"
  assertEq "1-arm match CC" r5.complexity 1
  assertEq "1-arm match depth" r5.maxDepth 0

  -- 5-arm flat match: CC = 5, depth = 1, pattern = flat-dispatch
  let r6 ← scanOne env
    "def f (n : Nat) : Nat := match n with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 4"
  assertEq "5-arm match CC" r6.complexity 5
  assertEq "5-arm match depth" r6.maxDepth 1
  assertEq "5-arm match pattern" r6.pattern .flatDispatch

  -- Flat match discount option
  let r6d ← scanOne env
    "def f (n : Nat) : Nat := match n with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 4"
    { flatMatchDiscount := true }
  assertEq "flatMatchDiscount raw CC" r6d.complexity 5
  assertEq "flatMatchDiscount effective CC" r6d.effectiveComplexity 2

  -- Equation compiler arms (3 cases => CC = 3)
  let r7 ← scanOne env "def fib : Nat → Nat | 0 => 0 | 1 => 1 | n + 2 => fib n"
  assertEq "equation arms CC" r7.complexity 3
  assertEq "equation arms depth" r7.maxDepth 1

  -- Pattern-matching lambda
  let r8 ← scanOne env "def f : Option Nat → Nat := fun | some n => n | none => 0"
  assertEq "fun match CC" r8.complexity 2

private def testDoAndBooleanConstructs (env : Environment) : IO Unit := do
  -- Boolean soup: &&, ||, <|>
  let rBool ← scanOne env
    "def check (a b c d : Bool) : Bool := (a && b) || (c && d) || a"
  assertEq "boolean soup CC" rBool.complexity 5
  assertEq "boolean soup pattern" rBool.pattern .booleanSoup

  let rOrElse ← scanOne env
    "def pick (a b c : Option Nat) : Option Nat := a <|> b <|> c"
  assertEq "orElse CC" rOrElse.complexity 3

  -- Rich `do` block: doIf (+1), elseIf (+1), doUnless (+1), doFor (+1), doLetElse (+1), tryCatch (+1) => CC = 7
  let doSrc :=
    "def proc (xs : List Nat) : IO Unit := do\n" ++
    "  if xs.isEmpty then return\n" ++
    "  else if xs.length == 1 then return\n" ++
    "  unless xs.length > 2 do return\n" ++
    "  for x in xs do\n" ++
    "    try\n" ++
    "      let some y := some x | continue\n" ++
    "      pure ()\n" ++
    "    catch _ => pure ()"
  let rDo ← scanOne env doSrc
  assertEq "do block CC" rDo.complexity 7
  assertEq "do block depth" rDo.maxDepth 2

  -- `doWhile`, `doRepeat`, `doLetArrow` with fallback, `doCatchMatch` (2 arms)
  let doSrc2 :=
    "def loop (m : IO (Option Nat)) : IO Nat := do\n" ++
    "  let mut i := 0\n" ++
    "  while i < 10 do i := i + 1\n" ++
    "  repeat\n" ++
    "    let some n ← m | break\n" ++
    "    try pure ()\n" ++
    "    catch\n" ++
    "      | IO.Error.userError _ => break\n" ++
    "      | _ => continue\n" ++
    "  return i"
  let rDo2 ← scanOne env doSrc2
  -- 1 + while(1) + repeat(1) + letArrowElse(1) + catchMatch(2) = 6
  assertEq "doWhile/repeat/catchMatch CC" rDo2.complexity 6

private def testDeepNestingAndPatterns (env : Environment) : IO Unit := do
  let deepSrc :=
    "def nested (a b c d : Bool) : Nat :=\n" ++
    "  if a then\n" ++
    "    if b then\n" ++
    "      if c then\n" ++
    "        if d then 1 else 2\n" ++
    "      else 3\n" ++
    "    else 4\n" ++
    "  else 5"
  let r ← scanOne env deepSrc { threshold := 10, maxDepth := 3 }
  assertEq "deep nesting CC" r.complexity 5
  assertEq "deep nesting depth" r.maxDepth 4
  assertEq "deep nesting pattern" r.pattern .deepNesting
  assertTrue "deep nesting triggers maxDepth warning" r.isWarning
  assertTrue "deep nesting produces suggestions" (!r.suggestions.isEmpty)

private def testProofsAndSignatures (env : Environment) : IO Unit := do
  -- `if` inside the theorem TYPE SIGNATURE must NOT be counted!
  let sigSrc :=
    "theorem sigTest (b : Bool) : (if b then 1 else 1) = 1 := by\n" ++
    "  cases b\n" ++
    "  · rfl\n" ++
    "  · rfl"
  let rSig ← scanOne env sigSrc
  assertEq "signature if ignored; cases = +1 => CC 2" rSig.complexity 2
  assertEq "theorem kind" rSig.kind .theoremDecl

  -- Rich tactic proof: induction(2 alts => +1), by_cases(+1), split(+1), first(2 => +1), try(+1) => CC = 6
  let proofSrc :=
    "theorem bigProof (n : Nat) (b : Bool) : True := by\n" ++
    "  induction n with\n" ++
    "  | zero => trivial\n" ++
    "  | succ k _ =>\n" ++
    "    by_cases h : b = true\n" ++
    "    · split <;> trivial\n" ++
    "    · try (first | trivial | exact True.intro)"
  let rProof ← scanOne env proofSrc { proofThreshold := 4 }
  assertEq "tactic proof CC" rProof.complexity 6
  assertEq "tactic proof pattern" rProof.pattern .tacticExplosion
  assertTrue "tactic proof warns over proofThreshold" rProof.isWarning

  -- `includeProofs := false` skips theorems
  let (repsSkip, _) ← scanSource env { includeProofs := false } "<test>" proofSrc
  assertEq "skip proofs yields 0 reports" repsSkip.size 0

private def testWhereMutualAndOverrides (env : Environment) : IO Unit := do
  -- `where` helper is scored separately from parent
  let whereSrc :=
    "def outer (x : Nat) : Nat := helper x where\n" ++
    "  helper (y : Nat) : Nat := if y > 0 then if y > 10 then 2 else 1 else 0"
  let (wReps, _) ← scanSource env {} "<test>" whereSrc
  assertEq "where decl produces 2 reports" wReps.size 2
  assertEq "outer CC is 1" wReps[0]!.complexity 1
  assertEq "helper name" wReps[1]!.name "outer.helper"
  assertEq "helper CC is 3" wReps[1]!.complexity 3

  -- `mutual` analyzes each member separately
  let mutSrc :=
    "mutual\n" ++
    "  def isEven : Nat → Bool | 0 => true | n + 1 => isOdd n\n" ++
    "  def isOdd : Nat → Bool | 0 => false | n + 1 => isEven n\n" ++
    "end"
  let (mReps, _) ← scanSource env {} "<test>" mutSrc
  assertEq "mutual produces 2 reports" mReps.size 2
  assertEq "isEven CC" mReps[0]!.complexity 2
  assertEq "isOdd CC" mReps[1]!.complexity 2

  -- Inline `set_option linter.cyclo false in` respected by CLI scanner
  let supSrc :=
    "set_option linter.cyclo false in\n" ++
    "def ignored (x : Nat) : Nat := if x == 0 then 1 else if x == 1 then 2 else 3\n" ++
    "def kept (x : Nat) : Nat := if x == 0 then 1 else 2"
  let (sReps, _) ← scanSource env { threshold := 1 } "<test>" supSrc
  assertEq "suppressed decl skipped by scanner" sReps.size 1
  assertEq "subsequent decl still scanned" sReps[0]!.name "kept"

private def testJsonAndDiagnostics (env : Environment) : IO Unit := do
  let r ← scanOne env
    "def demo (x : Nat) : Nat := if x == 0 then 1 else if x == 1 then 2 else 3"
    { threshold := 2, emitJson := true }
  let msg := formatLinterMessage r (emitJson := true)
  assertTrue "diagnostic contains [cyclo]" ((msg.splitOn "[cyclo]").length > 1)
  assertTrue "diagnostic contains Hotspots:" ((msg.splitOn "Hotspots:").length > 1)
  assertTrue "diagnostic contains Refactor options:" ((msg.splitOn "Refactor options:").length > 1)
  assertTrue "diagnostic contains JSON:" ((msg.splitOn "JSON:").length > 1)
  let jsonStr := (toJson r).compress
  match Json.parse jsonStr with
  | .error e => throw <| IO.userError s!"Invalid JSON output: {e}"
  | .ok j =>
    assertTrue "JSON has complexity field" (j.getObjVal? "complexity").isOk
    assertTrue "JSON has hotspots field" (j.getObjVal? "hotspots").isOk
    assertTrue "JSON has suggestions field" (j.getObjVal? "suggestions").isOk

def main : IO UInt32 := do
  let env ← mkParserEnvironment
  testTermConstructs env
  testDoAndBooleanConstructs env
  testDeepNestingAndPatterns env
  testProofsAndSignatures env
  testWhereMutualAndOverrides env
  testJsonAndDiagnostics env
  IO.println "All lean-cyclo tests passed!"
  return 0
