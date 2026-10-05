/-
  Trust-Lean — Tests/Properties/CBackendRefactor.lean
  N9.2: Property tests for CBackend refactored emission (stmtToC, exprToC, varNameToC).

  SlimCheck/Plausible tactic not available in this build.
  Using decidable examples and #eval-based exhaustive checks instead.
-/

import TrustLean.Backend.CBackend
import TrustLean.Backend.CBackendProperties

set_option autoImplicit false

namespace TrustLean.Tests.Properties.CBackendRefactor

/-! ## P1 — P0 INVARIANT: varNameToC output is not a C keyword -/
-- NOT_YET_RUNNABLE for universal quantifier (no SampleableExt for VarName)
-- Testing with representative examples and the formally proved theorem

-- varNameToC keeps a valid, non-reserved .user name outside the tl_ namespace and
-- prints every other one as tl_u plus its escape; temps print tl_tN, arrays base[idx].

-- Verify .user cases via exact value checks
example : varNameToC (.user "while") = "tl_uwhile" := by decide
example : varNameToC (.user "for") = "tl_ufor" := by decide
example : varNameToC (.user "int") = "tl_uint" := by decide
example : varNameToC (.user "tl_int") = "tl_utl_00005fint" := by decide
example : varNameToC (.user "x") = "x" := by decide

-- Verify .temp cases
example : varNameToC (.temp 0) = "tl_t0" := by decide
example : varNameToC (.temp 5) = "tl_t5" := by decide

-- Verify .array cases
example : varNameToC (.array "mem" 3) = "mem[3]" := by decide

-- P0 INVARIANT: sanitizeIdentifier_not_keyword is formally proved.
-- Here we just re-export the check.
example : sanitizeIdentifier "while" ∉ c99Keywords := by decide
example : sanitizeIdentifier "int" ∉ c99Keywords := by decide
example : sanitizeIdentifier "for" ∉ c99Keywords := by decide

#eval show IO Unit from do
  -- Exhaustive check: no keyword survives varNameToC
  let keywords := c99Keywords ++ cReservedExtra
  let mut failures := #[]
  for kw in keywords do
    let result := varNameToC (.user kw)
    if keywords.contains result then
      failures := failures.push (kw, result)
  if failures.isEmpty then
    IO.println s!"P1 INVARIANT (not keyword): PASS (all {keywords.length} keywords)"
  else
    IO.println s!"P1 INVARIANT: FAIL on {failures}"

/-! ## P2 — P0 INVARIANT: varNameToC output is a valid C identifier -/
-- sanitizeIdentifier_valid is formally proved in Common.lean.

example : isValidCIdent (varNameToC (.user "while")) = true := by decide
example : isValidCIdent (varNameToC (.user "")) = true := by decide
example : isValidCIdent (varNameToC (.user "2x")) = true := by decide
example : isValidCIdent (varNameToC (.user "a-b")) = true := by decide
example : isValidCIdent (varNameToC (.user "hello")) = true := by decide

#eval show IO Unit from do
  let inputs := ["while", "for", "int", "2bad", "", "a-b", "tl_x", "_x",
                  "main", "void", "!@#$%^", "v*o*i*d", "my_variable_name"]
  let mut failures := #[]
  for s in inputs do
    let result := varNameToC (.user s)
    if !isValidCIdent result then
      failures := failures.push (s, result)
  if failures.isEmpty then
    IO.println s!"P2 INVARIANT (valid C ident): PASS (all {inputs.length} samples)"
  else
    IO.println s!"P2 INVARIANT: FAIL on {failures}"

/-! ## P3 — P0 INJECTIVITY: distinct variables print distinctly (varNameToC_injective) -/

example : varNameToC (.user "int") ≠ varNameToC (.user "tl_int") := by decide
example : varNameToC (.temp 0) ≠ varNameToC (.user "t0") := by decide
example : varNameToC (.user "tl_t0") ≠ varNameToC (.temp 0) := by decide
example : varNameToC (.user "a[1]") ≠ varNameToC (.array "a" 1) := by decide

#eval show IO Unit from do
  let names : List VarName :=
    (["while", "for", "int", "tl_int", "2bad", "", "a-b", "a_b", "tl_x", "_x", "main",
      "void", "!@#$%^", "v*o*i*d", "my_variable_name", "t0", "tl_t0", "tl_u", "a[1]"].map .user) ++
    [.temp 0, .temp 1, .temp 10, .array "a" 1, .array "a" (-1), .array "a[1" 1]
  let mut failures := #[]
  for v in names do
    for w in names do
      if v != w && varNameToC v == varNameToC w then
        failures := failures.push (varNameToC v)
  if failures.isEmpty then
    IO.println s!"P3 INJECTIVITY: PASS (all {names.length * names.length} pairs)"
  else
    IO.println s!"P3 INJECTIVITY: FAIL on {failures}"

/-! ## P4 — P0 INVARIANT: stmtToC balanced braces -/
-- Formal theorem not available for general case (would need structural induction
-- + countChar lemmas for joinCode). Tested concretely here.

-- Concrete balanced brace checks (from CBackendProperties.lean)
example : countChar '{' (stmtToC 0 .skip) = countChar '}' (stmtToC 0 .skip) := by decide
example : countChar '{' (stmtToC 0 .break_) = countChar '}' (stmtToC 0 .break_) := by decide
example : countChar '{' (stmtToC 0 .continue_) = countChar '}' (stmtToC 0 .continue_) := by decide
example : countChar '{' (stmtToC 0 (.return_ none)) = countChar '}' (stmtToC 0 (.return_ none)) := by decide
example : countChar '{' (stmtToC 0 (.ite (.litBool true) .skip .skip))
    = countChar '}' (stmtToC 0 (.ite (.litBool true) .skip .skip)) := by decide
example : countChar '{' (stmtToC 0 (.while (.litBool true) .skip))
    = countChar '}' (stmtToC 0 (.while (.litBool true) .skip)) := by decide
example : countChar '{' (stmtToC 0 (.for_ .skip (.litBool true) .skip .skip))
    = countChar '}' (stmtToC 0 (.for_ .skip (.litBool true) .skip .skip)) := by decide

-- Complex nested case
example : countChar '{' (stmtToC 0 (.while (.litBool true) (.ite (.litBool false) .break_ .continue_)))
    = countChar '}' (stmtToC 0 (.while (.litBool true) (.ite (.litBool false) .break_ .continue_))) := by decide

#eval show IO Unit from do
  -- Test balanced braces on a broader set of statements
  let stmts : List Stmt := [
    .skip,
    .break_,
    .continue_,
    .return_ none,
    .return_ (some (.litInt 42)),
    .assign (.user "x") (.litInt 1),
    .ite (.litBool true) .skip .skip,
    .while (.litBool false) .skip,
    .for_ .skip (.litBool true) .skip .skip,
    .seq .skip .skip,
    .seq (.ite (.litBool true) .break_ .skip) (.while (.litBool false) .skip),
    .while (.litBool true) (.ite (.litBool false) .break_ .continue_),
    .call (.user "r") "func" [.litInt 1, .litInt 2],
    .store (.varRef (.user "arr")) (.litInt 0) (.litInt 42),
    .load (.user "x") (.varRef (.user "arr")) (.litInt 0)
  ]
  let mut failures := #[]
  for s in stmts do
    let code := stmtToC 0 s
    let opens := countChar '{' code
    let closes := countChar '}' code
    if opens != closes then
      failures := failures.push (repr s, opens, closes)
  if failures.isEmpty then
    IO.println s!"P4 INVARIANT (balanced braces): PASS (all {stmts.length} stmts)"
  else
    IO.println s!"P4 INVARIANT: FAIL on {failures}"

/-! ## P5 — P1 SOUNDNESS: Integer constants correctly represented -/

example : exprToC (.litInt 0) = "0" := by decide
example : exprToC (.litInt 42) = "42" := by decide
-- Negative int: decide doesn't reduce for negative Int literals with toString.
-- Verified via #eval below and by exprToC_litInt_neg theorem.
example : exprToC (.litBool true) = "1" := by decide
example : exprToC (.litBool false) = "0" := by decide

#eval show IO Unit from do
  let tests : List (Int × String) := [
    (0, "0"), (1, "1"), (42, "42"), (100, "100"),
    (-1, "(-1)"), (-42, "(-42)"), (-100, "(-100)")
  ]
  let mut failures := #[]
  for (n, expected) in tests do
    let result := exprToC (.litInt n)
    if result != expected then
      failures := failures.push (n, expected, result)
  if failures.isEmpty then
    IO.println s!"P5 SOUNDNESS (int constants): PASS (all {tests.length} cases)"
  else
    IO.println s!"P5 SOUNDNESS: FAIL on {failures}"

/-! ## P6 — P2 INVARIANT: generateCFunction produces non-empty string -/

#eval show IO Unit from do
  let cfg := CConfig.mk true true
  let tests := [
    ("f", [("x", "int64_t")], Stmt.assign (.user "x") (.litInt 1)),
    ("g", [], Stmt.skip),
    ("h", [("a", "int64_t"), ("b", "int64_t")], Stmt.seq (.assign (.user "a") (.litInt 0)) (.assign (.user "b") (.litInt 1)))
  ]
  let mut failures := #[]
  for (name, params, body) in tests do
    let result := generateCFunction cfg name params body (.litInt 0)
    if result.isEmpty then
      failures := failures.push name
  if failures.isEmpty then
    IO.println s!"P6 INVARIANT (non-empty function): PASS (all {tests.length} cases)"
  else
    IO.println s!"P6 INVARIANT: FAIL on {failures}"

end TrustLean.Tests.Properties.CBackendRefactor
