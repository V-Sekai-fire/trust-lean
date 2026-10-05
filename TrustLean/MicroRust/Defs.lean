/-
  Trust-Lean — Verified Code Generation Framework
  MicroRust/Defs.lean: Type aliases and Rust-specific identifier mapping

  N24.1 (v4.0.0): FUND — MicroRust reuses the language-neutral MicroC AST
  and evaluators. This file provides readability aliases and the Rust-specific
  identifier mapping (varNameToRust over rustReservedIdentifiers).
-/

import TrustLean.MicroC.AST
import TrustLean.Backend.Common
import TrustLean.Backend.RustBackend

set_option autoImplicit false

namespace TrustLean

/-! ## Type Aliases (readability, zero cost) -/

/-- MicroRust shares the MicroC AST — the types are language-neutral. -/
abbrev MicroRustExpr := MicroCExpr
abbrev MicroRustStmt := MicroCStmt
abbrev MicroRustEnv := MicroCEnv
abbrev MicroRustBinOp := MicroCBinOp
abbrev MicroRustUnaryOp := MicroCUnaryOp

/-! ## Rust-Specific Identifier Mapping -/

/-- Map a VarName to a Rust identifier string, with the same scheme as `varNameToC`
    over the Rust reserved identifiers. -/
def varNameToRust : VarName → String
  | .user s => userIdent rustReservedIdentifiers s
  | .temp k => tempIdent k
  | .array base idx => base ++ "[" ++ toString idx ++ "]"

/-- Distinct variables print to distinct Rust identifiers. -/
theorem varNameToRust_injective : Function.Injective varNameToRust :=
  varNameIdent_injective rustReservedIdentifiers varNameToRust
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

/-- BinOp mapping to MicroRust uses the same MicroC mapping (operators are identical). -/
abbrev binOpToMicroRust := binOpToMicroC

/-- UnaryOp mapping to MicroRust uses the same MicroC mapping (operators are identical). -/
abbrev unaryOpToMicroRust := unaryOpToMicroC

/-! ## varNameToRust @[simp] Equation Lemmas -/

@[simp] theorem varNameToRust_user (s : String) :
    varNameToRust (.user s) = userIdent rustReservedIdentifiers s := rfl

@[simp] theorem varNameToRust_temp (n : Nat) :
    varNameToRust (.temp n) = tempIdent n := rfl

@[simp] theorem varNameToRust_array (s : String) (n : Nat) :
    varNameToRust (.array s n) = varNameToStr (.array s n) := rfl

end TrustLean
