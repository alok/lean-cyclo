# `lean-cyclo`

**AI-first cyclomatic complexity linter and CLI for Lean 4 — built by AI, for AI (and humans who hate tangled Lean code).**

`lean-cyclo` measures exact Lean-4-native McCabe cyclomatic complexity, branch nesting depth, construct breakdowns, and root-cause complexity patterns across functional terms, `do`-notation, and tactic proofs. Every warning tells an AI coding agent *where* the complexity lives (`L<line>:<col>`), *why* it spiked (`deep-nesting`, `flat-dispatch`, `boolean-soup`, `imperative-loop-nest`, `error-handling-heavy`, `tactic-explosion`, `mixed-branching`), *how* to refactor it in idiomatic Lean 4, and the exact local override if high branching is intentional.

Zero external dependencies — pure Lean 4 (`import Lean`), parsed with Lean's real parser.

---

## Quick Start

### 1. Add from Reservoir (or Git)

In `lakefile.toml`:
```toml
[[require]]
name = "lean-cyclo"
scope = "alok"
```

Or in `lakefile.lean`:
```lean
require "alok" / "lean-cyclo"
```

*(Before Reservoir's daily crawler indexes the repo, you can also depend on it directly via Git: `git = "https://github.com/alok/lean-cyclo"`.)*

### 2. Mode A — Native Lean 4 Command Linter

Import `Cyclo` in any module (or your root library file) to get inline LSP / `lake build` warnings:

```lean
import Cyclo
```

Configure globally in `lakefile.toml`:
```toml
[leanOptions]
"weak.linter.cyclo" = true
"weak.linter.cyclo.threshold" = 10
"weak.linter.cyclo.proofThreshold" = 15
```

### 3. Mode B — Standalone CLI & `lake lint` Driver

Wire `lean-cyclo` as your project's Lake lint driver in `lakefile.toml`:
```toml
lintDriver = "lean-cyclo/cyclo"
```

Then run:
```bash
lake lint                                     # AI-first compact agent brief (exits 1 on warnings)
lake exe cyclo --format json src/             # Machine-readable JSON report
lake exe cyclo --format text --all --top 10   # Human report of top 10 complex declarations
lake exe cyclo --no-proofs --threshold 12     # Code-only scan with custom budget
lake exe cyclo --max-depth 4 --no-fail        # Non-failing audit flagging deep nesting
```

---

## Example Diagnostic (Live Lean Linter)

```text
warning: Main.lean:64:2: [cyclo] `parseCli.go` (where) cyclomatic complexity = 14 (threshold: 10, max_depth: 2, pattern: flat-dispatch)
Triggered: complexity 14 > threshold 10
Breakdown (+13 decision points): term:+13
Hotspots:
  1. L64:3  +12  equation arms (13 cases) [depth 1]
  2. L90:7  +1  if/then/else [depth 2]
Refactor options:
  - [split-dispatch-by-domain] Group arms of equation arms (13 cases) at L64-L93 into domain-specific `where` helpers or a lookup table.
    Impact: Keeps top-level dispatch flat while moving per-case logic out of the main body (currently +12 branches).
  - [document-intentional-dispatch] If exhaustive enum dispatch is intentional, raise this declaration's local budget with `set_option linter.cyclo.threshold <N> in` or enable `linter.cyclo.flatMatchDiscount`.
    Impact: Avoids fighting legitimate AST/opcode evaluators.
Local override: `set_option linter.cyclo.threshold 14 in` or `set_option linter.cyclo false in`

Note: This linter can be disabled with `set_option linter.cyclo false`
```

## Example Agent Brief (`--format agent`, default for CLI)

```text
CYCLO WARN | files=9 decls=100 warnings=2 max_cc=14

WARN ./MyApp/Eval.lean:42:1 `MyApp.eval` (def) CC=14/10 depth=4 lines=48 pattern=deep-nesting
  breakdown: term:+6, do:+4, bool:+3
  hotspots: L55:9 +1 do if (d4) | L48:5 +4 match (5 arms) (d2) | L59:12 +1 && (d4)
  fix[extract-deep-branch]: Extract the nested `do if` block at L55-L66 (depth 4) into a named `where` or `private def` helper.
  fix[invert-guards]: Replace nested `if` / `if let` checks with early-return guard clauses (`if !cond then return ...` or `let some x := e | return ...`).
```

---

## Lean-4-Native McCabe Complexity Rules

Every declaration starts at base complexity **1** and adds decision-point deltas from its **body only** (type signatures are excluded so `if`/`match` inside theorem statements never penalize you):

| Category | Lean 4 Construct | Delta | Notes |
| --- | --- | --- | --- |
| **Term** | `if ... then ... else ...`, `if h : ...`, `if let ...` | `+1` | Flat `else if` chains add `+1` each without inflating nesting depth |
| **Term** | `match` / `match_expr` / `fun \| ...` / equation arms (`k` arms) | `+(k - 1)` | 1-arm destructuring (`match p with \| (a, b) => ...`) is `+0` |
| **`do` Control** | `do if`, `else if`, `unless`, `for`, `while`, `repeat` | `+1` | Tracks nesting depth across `do` blocks |
| **Error Handling** | `let pat := e \| fallback`, `let pat ← m \| fallback`, `catch` | `+1` | `catch \| p1 => ... \| p2 => ...` adds `+k` exceptional paths; `finally` adds `+0` |
| **Boolean** | `&&`, `\|\|`, `<\|>` | `+1` | Counts short-circuit / alternative paths without inflating depth |
| **Tactic Proofs** | `cases`, `induction`, `split`, `by_cases`, `match`, `first`, `try`, `repeat`, `<\|>` | `+(k - 1)` or `+1` | Configurable separate budget (`proofThreshold := 15`) or disable with `includeProofs := false` |
| **Structure** | `where` helpers & `mutual` blocks | Separate units | Extracting a `where` helper immediately lowers the parent's complexity |

---

## Options & CLI Flags

### Lean `set_option` Knobs

| Option | Default | Description |
| --- | --- | --- |
| `linter.cyclo` | `true` | Enable/disable the linter (integrates with `linter.all`) |
| `linter.cyclo.threshold` | `10` | Max CC for code declarations (`def`, `abbrev`, `instance`, `opaque`, `example`, `where`) |
| `linter.cyclo.proofThreshold` | `15` | Max CC for `theorem` declarations |
| `linter.cyclo.includeProofs` | `true` | Analyze `theorem` declarations |
| `linter.cyclo.maxDepth` | `0` | Standalone max nesting-depth trigger (`0` = advisory only) |
| `linter.cyclo.flatMatchDiscount` | `false` | Discount flat top-level `match` / equation tables to `+1` |
| `linter.cyclo.json` | `false` | Append a compact JSON payload to each Lean linter diagnostic |
| `linter.cyclo.reportAll` | `false` | Emit info-level complexity telemetry for every declaration |

Local scoped overrides work identically in both the live Lean linter and the standalone CLI scanner:
```lean
set_option linter.cyclo.flatMatchDiscount true in
def evalOpcode : Opcode → State → State
  | ...

set_option linter.cyclo.threshold 16 in
def complexParser ...

set_option linter.cyclo false in
def intentionallyUnrolled ...
```

### CLI Flags (`lake exe cyclo` / `lake lint -- ...`)

- `--format <agent|text|json>` (default: `agent`)
- `--json` (shorthand for `--format json`)
- `--threshold <N>` (default: `10`)
- `--proof-threshold <N>` (default: `15`)
- `--max-depth <N>` (default: `0`)
- `--no-proofs`
- `--flat-match-discount`
- `--all` (include declarations within budget)
- `--top <N>` (show top `N` highest-complexity declarations)
- `--no-fail` (exit `0` even when warnings are found)

---

## Agent Integration (`AGENTS.md` / `CLAUDE.md`)

Drop this snippet into your repo's `AGENTS.md` or `CLAUDE.md`:

```markdown
## Complexity Gate
Run `lake exe cyclo --format agent` (or `lake lint`) after refactoring Lean code.
- Fix `deep-nesting`, `boolean-soup`, and `mixed-branching` warnings by extracting `where` helpers or early-return `let ... | return ...` guards.
- For intentional exhaustive enum/AST dispatch tables, use `set_option linter.cyclo.flatMatchDiscount true in` rather than disabling the linter globally.
```

---

## Development

```bash
lake build   # Build Cyclo library and cyclo CLI
lake test    # Run compile-time #guard_msgs linter tests + unit tests
lake lint    # Dogfood lean-cyclo on itself (passes with 0 warnings)
```

## License

Apache-2.0 — see [LICENSE](LICENSE).
