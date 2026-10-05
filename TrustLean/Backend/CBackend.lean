/-
  Trust-Lean — Verified Code Generation Framework
  Backend/CBackend.lean: C code generation from Core IR

  N4.1 (v1.0.0): C backend (C99/C11 compatible).
  N9.2 (v1.2.0): Industrial upgrade — sanitized identifiers, autocontained headers,
  mandatory braces on all control flow. All 12 Stmt constructors handled.
  Based on LeanScribe's CBackend.lean, extended for Trust-Lean's full IR.
  The BackendEmitter instance prints through stmtToMicroC and microCToString, whose output
  the roundtrip theorems cover, after a declaration for every local.
-/

import TrustLean.Backend.Common
import TrustLean.Core.Stmt
import TrustLean.Typeclass.BackendEmitter
import TrustLean.MicroC.Translation
import TrustLean.MicroC.Typed

set_option autoImplicit false

namespace TrustLean

/-! ## C Configuration -/

/-- Configuration for the C backend. -/
structure CConfig where
  /-- Use int64_t (true) or long long (false) for integers. -/
  useInt64 : Bool := true
  /-- Include power helper function in output. -/
  includePowerHelper : Bool := true
  deriving Repr

/-- The field defaults. A derived instance would set both fields to `false`. -/
instance : Inhabited CConfig := ⟨{}⟩

/-- Integer type name based on config. -/
def CConfig.intType (cfg : CConfig) : String :=
  if cfg.useInt64 then "int64_t" else "long long"

/-! ## Operator Conversion -/

/-- Convert a BinOp to the corresponding C infix operator. -/
def binOpToC : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .eqOp => "=="
  | .ltOp => "<"
  | .land => "&&"
  | .lor => "||"
  | .band => "&"
  | .bor => "|"
  | .bxor => "^"
  | .bshl => "<<"
  | .bshr => ">>"

/-- Convert a UnaryOp to the corresponding C prefix operator. Both casts compute `n % 2^32`. -/
def unaryOpToC : UnaryOp → String
  | .neg => "-"
  | .lnot => "!"
  | .widen32to64 => "(int64_t)(uint32_t)"
  | .trunc64to32 => "(uint32_t)"

/-! ## Expression Emission -/

/-- Convert a LowLevelExpr to a C expression string.
    All binary sub-expressions are fully parenthesized to avoid precedence ambiguity.
    Unary operations are parenthesized. Negative literals are parenthesized. -/
def exprToC : LowLevelExpr → String
  | .litInt n => if n < 0 then s!"({n})" else s!"{n}"
  | .litBool true => "1"
  | .litBool false => "0"
  | .varRef v => varNameToC v
  | .binOp op lhs rhs =>
    "(" ++ exprToC lhs ++ " " ++ binOpToC op ++ " " ++ exprToC rhs ++ ")"
  | .unaryOp op e => "(" ++ unaryOpToC op ++ exprToC e ++ ")"
  | .powCall base n => "power(" ++ exprToC base ++ ", " ++ toString n ++ ")"
  | .addrOf v => "&" ++ varNameToC v

/-! ## Statement Emission -/

/-- Convert a Stmt to C source code at the given indentation level.
    Handles all 12 Stmt constructors. Mandatory braces on all control flow.
    Variables print via varNameToC. -/
def stmtToC (level : Nat) : Stmt → String
  | .skip => ""
  | .assign name expr =>
    indentStr level ++ varNameToC name ++ " = " ++ exprToC expr ++ ";"
  | .store base idx val =>
    indentStr level ++ exprToC base ++ "[" ++ exprToC idx ++ "] = " ++ exprToC val ++ ";"
  | .load var base idx =>
    indentStr level ++ varNameToC var ++ " = " ++
      exprToC base ++ "[" ++ exprToC idx ++ "];"
  | .seq s1 s2 => joinCode (stmtToC level s1) (stmtToC level s2)
  | .ite cond thenB elseB =>
    let pad := indentStr level
    let tc := stmtToC (level + 1) thenB
    let ec := stmtToC (level + 1) elseB
    pad ++ "if (" ++ exprToC cond ++ ") {\n" ++ tc ++ "\n" ++
    pad ++ "} else {\n" ++ ec ++ "\n" ++ pad ++ "}"
  | .while cond body =>
    let pad := indentStr level
    let bc := stmtToC (level + 1) body
    pad ++ "while (" ++ exprToC cond ++ ") {\n" ++ bc ++ "\n" ++ pad ++ "}"
  | .for_ init cond step body =>
    let initC := stmtToC level init
    let bodyC := stmtToC (level + 1) body
    let stepC := stmtToC (level + 1) step
    let pad := indentStr level
    let innerBody := joinCode bodyC stepC
    let whileBlock := pad ++ "while (" ++ exprToC cond ++ ") {\n" ++
      innerBody ++ "\n" ++ pad ++ "}"
    joinCode initC whileBlock
  | .call result fname args =>
    let argsStr := ", ".intercalate (args.map exprToC)
    indentStr level ++ varNameToC result ++ " = " ++
      sanitizeIdentifier fname ++ "(" ++ argsStr ++ ");"
  | .break_ => indentStr level ++ "break;"
  | .continue_ => indentStr level ++ "continue;"
  | .return_ (some e) => indentStr level ++ "return " ++ exprToC e ++ ";"
  | .return_ none => indentStr level ++ "return;"

/-! ## Structural Properties -/

/-- stmtToC on skip produces an empty string. -/
@[simp] theorem stmtToC_skip (level : Nat) : stmtToC level .skip = "" := rfl

/-- stmtToC on break_ produces indented "break;". -/
@[simp] theorem stmtToC_break (level : Nat) :
    stmtToC level .break_ = indentStr level ++ "break;" := rfl

/-- stmtToC on continue_ produces indented "continue;". -/
@[simp] theorem stmtToC_continue (level : Nat) :
    stmtToC level .continue_ = indentStr level ++ "continue;" := rfl

/-- stmtToC on return_ none produces indented "return;". -/
@[simp] theorem stmtToC_return_none (level : Nat) :
    stmtToC level (.return_ none) = indentStr level ++ "return;" := rfl

/-! ## Function Generation -/

/-- Build a comma-separated C parameter list, each name printed as the body prints
    that user variable. Each pair is (name, type), e.g., ("x", "int64_t"). -/
private def buildParamList (params : List (String × String)) : String :=
  ", ".intercalate (params.map fun (n, t) => t ++ " " ++ varNameToC (.user n))

/-- Variables an expression reads. An array's base names the array, not a scalar. -/
def MicroCExpr.scalarVars : MicroCExpr → List String
  | .varRef x => [x]
  | .binOp _ l r => l.scalarVars ++ r.scalarVars
  | .unaryOp _ e => e.scalarVars
  | .powCall b _ => b.scalarVars
  | .arrayAccess _ i => i.scalarVars
  | _ => []

/-- Variables a statement reads or writes. -/
def MicroCStmt.scalarVars : MicroCStmt → List String
  | .assign x e => x :: e.scalarVars
  | .store _ i v => i.scalarVars ++ v.scalarVars
  | .load x _ i => x :: i.scalarVars
  | .call x _ args => x :: args.flatMap MicroCExpr.scalarVars
  | .seq s1 s2 => s1.scalarVars ++ s2.scalarVars
  | .ite c t e => c.scalarVars ++ t.scalarVars ++ e.scalarVars
  | .while_ c b => c.scalarVars ++ b.scalarVars
  | .return_ (some e) => e.scalarVars
  | _ => []

/-- The type of the first assignment to `x` whose right side types under `Γ`. -/
def MicroCStmt.assignedTy (Γ : CDecls) (x : String) : MicroCStmt → Option CType
  | .assign y e => if y = x then (exprTy Γ e).map (·.1) else none
  | .seq s1 s2 | .ite _ s1 s2 => (s1.assignedTy Γ x).orElse fun _ => s2.assignedTy Γ x
  | .while_ _ b => b.assignedTy Γ x
  | _ => none

/-- Call names through `sanitizeIdentifier`, as `stmtToC` printed them. -/
def MicroCStmt.sanitizeCalls : MicroCStmt → MicroCStmt
  | .call r f args => .call r (sanitizeIdentifier f) args
  | .seq s1 s2 => .seq s1.sanitizeCalls s2.sanitizeCalls
  | .ite c t e => .ite c t.sanitizeCalls e.sanitizeCalls
  | .while_ c b => .while_ c b.sanitizeCalls
  | s => s

/-- The type of a parameter, from the type name it is declared with. -/
def paramCType (t : String) : Option CType :=
  if t = "long long" then some .i64 else CType.ofName t

/-- Declarations for the scalars a body uses besides its parameters. Each takes the type of
    its first assignment that types, with the other declarations as the last pass left them,
    and `int64_t` when none types. -/
def localDecls (params : CDecls) (paramNames : List String) (body : MicroCStmt)
    (result : MicroCExpr) : CDecls :=
  let names := ((body.scalarVars ++ result.scalarVars).filter fun x =>
    isValidCIdent x && !paramNames.contains x).eraseDups
  let pass := fun (Γ : CDecls) => names.map fun x => (x, (body.assignedTy (params ++ Γ) x).getD .i64)
  (List.range names.length).foldl (fun Γ _ => pass Γ) (names.map (·, .i64))

/-- Generate a complete C function wrapping a statement body and return expression.
    The body and the return print through `microCToString`, after a declaration for every
    other scalar the body uses. `(void)power;` marks the header's helper used, which clang's
    `-Wunused-function` otherwise rejects in a function that does not call it. The function
    name is sanitized; parameter names print via varNameToC. -/
def generateCFunction (cfg : CConfig) (funcName : String)
    (params : List (String × String)) (body : Stmt) (result : LowLevelExpr) : String :=
  let safeName := sanitizeIdentifier funcName
  let signature := cfg.intType ++ " " ++ safeName ++ "(" ++ buildParamList params ++ ")"
  let paramNames := params.map fun (n, _) => varNameToC (.user n)
  let paramDecls := params.filterMap fun (n, t) => (paramCType t).map (varNameToC (.user n), ·)
  let ms := (stmtToMicroC body).sanitizeCalls
  let r := exprToMicroC result
  signature ++ " {\n" ++ (if cfg.includePowerHelper then "(void)power;\n" else "") ++
    printTyped (localDecls paramDecls paramNames ms r) ms ++ "\n" ++
    microCToString (.return_ (some r)) ++ "\n}"

/-- Generate C preamble with necessary includes and the assertions the typed subset relies on:
    `uint32_t` arithmetic does not promote to `int`, and `nu` is a `uint32_t` value.
    The power helper squares `base` only while a higher exponent bit remains, so it overflows
    only when the result does. -/
def generateCHeader (cfg : CConfig) : String :=
  let base := "#include <stdint.h>\n#include <stdbool.h>\n#include <stdlib.h>\n#include <limits.h>\n\n" ++
    "_Static_assert(INT_MAX < UINT32_MAX, \"uint32_t does not promote to int (C11 6.3.1.1p2)\");\n" ++
    "_Static_assert(sizeof(unsigned) == 4 && UINT_MAX == UINT32_MAX, " ++
    "\"a u-suffixed literal below 2^32 is a 32-bit unsigned int (C11 6.4.4.1p5)\");"
  if cfg.includePowerHelper then
    base ++ "\n\n" ++
    "static " ++ cfg.intType ++ " power(" ++ cfg.intType ++ " base, unsigned int exp) {\n" ++
    "  " ++ cfg.intType ++ " result = 1;\n" ++
    "  while (exp > 0) {\n" ++
    "    if (exp % 2 == 1) result *= base;\n" ++
    "    exp /= 2;\n" ++
    "    if (exp > 0) base *= base;\n" ++
    "  }\n" ++
    "  return result;\n" ++
    "}"
  else base

/-! ## BackendEmitter Instance -/

/-- C backend implements BackendEmitter through the printer the roundtrip theorems cover. -/
instance : BackendEmitter CConfig where
  name := "C"
  emitStmt _cfg level stmt := indentStr level ++ microCToString (stmtToMicroC stmt).sanitizeCalls
  emitFunction cfg name params body result := generateCFunction cfg name params body result
  emitHeader cfg := generateCHeader cfg

end TrustLean
