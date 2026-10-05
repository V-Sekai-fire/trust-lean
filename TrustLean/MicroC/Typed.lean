/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/Typed.lean: typed declarations for MicroC programs

  A typed program is a declaration list and a body. Each variable is `uint32_t`, `int64_t` or
  `bool`; the operands of a binary operator share a type; the two casts are the only
  conversions. The printed form declares every variable, initialised to its type's zero,
  ahead of the body that `microCToString` prints.
-/

import TrustLean.MicroC.PrettyPrint
import TrustLean.MicroC.Int64
import TrustLean.Backend.Common

set_option autoImplicit false

namespace TrustLean

/-! ## Types and Declarations -/

/-- The C types a typed program declares. -/
inductive CType where
  | u32
  | i64
  | bool
  deriving Repr, DecidableEq, Inhabited

def CType.name : CType → String
  | .u32 => "uint32_t"
  | .i64 => "int64_t"
  | .bool => "bool"

def CType.ofName : String → Option CType
  | "uint32_t" => some .u32
  | "int64_t" => some .i64
  | "bool" => some .bool
  | _ => none

/-- The literal a declaration initialises its variable to: `0u`, `0` or `false`. -/
def CType.zero : CType → MicroCExpr
  | .u32 => .litU32 0
  | .i64 => .litInt 0
  | .bool => .litBool false

/-- A declaration list: each variable with its type, in printing order. -/
abbrev CDecls := List (String × CType)

theorem lookup_mem {Γ : CDecls} {x : String} {t : CType} (h : Γ.lookup x = some t) :
    (x, t) ∈ Γ := by
  induction Γ with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨y, u⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hxy
      simp only [beq_iff_eq] at hxy
      simp only [Option.some.injEq] at h
      subst hxy h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

/-- The environment a typed program starts in: each declared variable holds its type's zero. -/
def typedDefault (Γ : CDecls) : MicroCEnv := fun x =>
  match Γ.lookup x with
  | some .bool => .bool false
  | _ => .int 0

/-! ## Expression Typing -/

def sameVar : MicroCExpr → MicroCExpr → Bool
  | .varRef a, .varRef b => a == b
  | _, _ => false

/-- A shift count is a literal below the width, or reads a variable: clang rejects a constant
    count outside `[0, width)` (`-Wshift-count-overflow`). -/
def shiftCountOk (r : MicroCExpr) (width : Nat) (readsVar : Bool) : Bool :=
  match r with
  | .litU32 n => decide (n.toNat < width)
  | .litInt n => decide (0 ≤ n ∧ n < width)
  | _ => readsVar

/-- The type of a binary operation whose operands both have type `t`.
    `int64_t` arithmetic needs an operand that reads a variable: two unsuffixed literals are
    `int` arithmetic in C, and a constant expression that overflows fails `-Winteger-overflow`.
    A comparison of a variable with itself fails `-Wtautological-compare`. -/
def binOpTy (op : MicroCBinOp) (l r : MicroCExpr) (t : CType) (vl vr : Bool) :
    Option (CType × Bool) :=
  match op, t with
  | .add, .u32 | .sub, .u32 | .mul, .u32 | .band, .u32 | .bor, .u32 | .bxor, .u32 =>
    some (.u32, vl || vr)
  | .add, .i64 | .sub, .i64 | .mul, .i64 | .band, .i64 | .bor, .i64 | .bxor, .i64 =>
    if vl || vr then some (.i64, true) else none
  | .bshl, .u32 | .bshr, .u32 =>
    if shiftCountOk r 32 vr then some (.u32, vl || vr) else none
  | .bshl, .i64 | .bshr, .i64 =>
    if vl && shiftCountOk r 64 vr then some (.i64, true) else none
  | .eqOp, .u32 | .ltOp, .u32 | .eqOp, .i64 | .ltOp, .i64 =>
    if sameVar l r then none else some (.bool, vl || vr)
  | .land, .bool | .lor, .bool => some (.bool, vl || vr)
  | _, _ => none

def unaryOpTy (op : MicroCUnaryOp) (t : CType) (v : Bool) : Option (CType × Bool) :=
  match op, t with
  | .neg, .u32 => some (.u32, v)
  | .neg, .i64 => some (.i64, v)
  | .lnot, .bool => some (.bool, v)
  | .widen32to64, .u32 => some (.i64, v)
  | .trunc64to32, .i64 => some (.u32, v)
  | _, _ => none

/-- A negated literal `-5` or `-5u` prints as text the parser reads differently. -/
def negOfLit : MicroCUnaryOp → MicroCExpr → Bool
  | .neg, .litInt n => decide (0 ≤ n)
  | .neg, .litU32 _ => true
  | _, _ => false

/-- The type of `e` under `Γ`, with whether it reads a variable (otherwise it is a C11 constant
    expression, 6.6). `none` outside the typed subset: an undeclared variable, operands of
    different types, an array access, or an `int64_t` literal that has no C type. -/
def exprTy (Γ : CDecls) : MicroCExpr → Option (CType × Bool)
  | .litInt n => if -maxInt64 ≤ n ∧ n ≤ maxInt64 then some (.i64, false) else none
  | .litU32 _ => some (.u32, false)
  | .litBool _ => some (.bool, false)
  | .varRef x => (Γ.lookup x).map fun t => (t, true)
  | .binOp op l r =>
    match exprTy Γ l, exprTy Γ r with
    | some (tl, vl), some (tr, vr) => if tl = tr then binOpTy op l r tl vl vr else none
    | _, _ => none
  | .unaryOp op e =>
    match exprTy Γ e with
    | some (t, v) => if negOfLit op e then none else unaryOpTy op t v
    | none => none
  | .powCall b n =>
    match exprTy Γ b with
    | some (.i64, _) => if n < 2 ^ 32 then some (.i64, true) else none
    | _ => none
  | .arrayAccess _ _ => none

/-! ## Statement Typing -/

def MicroCStmt.isSeq : MicroCStmt → Bool
  | .seq _ _ => true
  | _ => false

def MicroCExpr.isPowCall : MicroCExpr → Bool
  | .powCall _ _ => true
  | _ => false

def condTy (Γ : CDecls) (c : MicroCExpr) : Bool :=
  match exprTy Γ c with
  | some (.bool, _) => true
  | _ => false

/-- A well-typed body: assignments of the variable's own type, `bool` conditions, `break` and
    `continue` only inside a loop, and sequences nested to the right as the parser rebuilds
    them. An assignment is not to itself (`-Wself-assign`) and its right side is not a bare
    `power(...)`, which prints like a call. Arrays, calls and `return` are outside the subset. -/
def stmtTy (Γ : CDecls) (inLoop : Bool) : MicroCStmt → Bool
  | .skip => true
  | .break_ => inLoop
  | .continue_ => inLoop
  | .assign x e =>
    match Γ.lookup x, exprTy Γ e with
    | some t, some (t', _) => t == t' && !sameVar (.varRef x) e && !e.isPowCall
    | _, _ => false
  | .seq s1 s2 => !s1.isSeq && stmtTy Γ inLoop s1 && stmtTy Γ inLoop s2
  | .ite c t e => condTy Γ c && stmtTy Γ inLoop t && stmtTy Γ inLoop e
  | .while_ c b => condTy Γ c && stmtTy Γ true b
  | _ => false

/-- A declared name: a lowercase letter, then letters, digits and underscores; not a C keyword,
    a header name or `power`; and not starting with `return`, which the parser reads as the
    keyword. -/
def declNameOk (x : String) : Bool :=
  match x.toList with
  | [] => false
  | c :: cs =>
    c.isLower && cs.all isValidCIdentChar && !cReservedIdentifiers.contains x &&
      x != "power" && x.toList.take 6 != "return".toList

def declsOk (Γ : CDecls) : Bool :=
  Γ.all (fun p => declNameOk p.1) && decide (Γ.map (·.1)).Nodup

/-! ## Short-Circuit Operands -/

/-- `op` on operands of type `t` has no undefined case: `int64_t` arithmetic can overflow, and a
    shift count that is not a literal can reach the width. -/
def binOpDefined (op : MicroCBinOp) (r : MicroCExpr) (t : CType) : Bool :=
  match op, t, r with
  | .eqOp, _, _ | .ltOp, _, _ | .land, _, _ | .lor, _, _ => true
  | .add, .u32, _ | .sub, .u32, _ | .mul, .u32, _ | .band, .u32, _ | .bor, .u32, _
  | .bxor, .u32, _ => true
  | .bshl, .u32, .litU32 _ | .bshr, .u32, .litU32 _ => true
  | _, _, _ => false

/-- `e` has a value in every environment where each variable holds a value of its type. -/
def MicroCExpr.definedOn (Γ : CDecls) : MicroCExpr → Bool
  | .binOp op l r => l.definedOn Γ && r.definedOn Γ &&
    match exprTy Γ l with
    | some (t, _) => binOpDefined op r t
    | none => false
  | .unaryOp .neg e => e.definedOn Γ && (exprTy Γ e).map (·.1) == some .u32
  | .unaryOp _ e => e.definedOn Γ
  | .powCall _ _ | .arrayAccess _ _ => false
  | _ => true

/-- The right operand of every `&&` and `||` is `definedOn Γ`. C evaluates it only when the left
    operand does not decide the result, and `evalTyped` evaluates it always. -/
def MicroCExpr.shortCircuitOk (Γ : CDecls) : MicroCExpr → Bool
  | .binOp op l r => l.shortCircuitOk Γ && r.shortCircuitOk Γ &&
    match op with
    | .land | .lor => r.definedOn Γ
    | _ => true
  | .unaryOp _ e | .powCall e _ => e.shortCircuitOk Γ
  | _ => true

def MicroCStmt.shortCircuitOk (Γ : CDecls) : MicroCStmt → Bool
  | .assign _ e => e.shortCircuitOk Γ
  | .seq s1 s2 => s1.shortCircuitOk Γ && s2.shortCircuitOk Γ
  | .ite c t e => c.shortCircuitOk Γ && t.shortCircuitOk Γ && e.shortCircuitOk Γ
  | .while_ c b => c.shortCircuitOk Γ && b.shortCircuitOk Γ
  | _ => true

/-- `s` is a well-typed program body under the declarations `Γ`. -/
def WellTyped (Γ : CDecls) (s : MicroCStmt) : Prop :=
  declsOk Γ = true ∧ stmtTy Γ false s = true ∧ s.shortCircuitOk Γ = true

instance (Γ : CDecls) (s : MicroCStmt) : Decidable (WellTyped Γ s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## The `uint32_t` Subset -/

/-- An expression of the `uint32_t` subset: no `int64_t` literal, cast, `power` or array. -/
def MicroCExpr.inU32Subset : MicroCExpr → Bool
  | .litU32 _ | .litBool _ | .varRef _ => true
  | .binOp _ l r => l.inU32Subset && r.inU32Subset
  | .unaryOp .neg e | .unaryOp .lnot e => e.inU32Subset
  | _ => false

def MicroCStmt.inU32Subset : MicroCStmt → Bool
  | .skip | .break_ | .continue_ => true
  | .assign _ e => e.inU32Subset
  | .seq s1 s2 => s1.inU32Subset && s2.inU32Subset
  | .ite c t e => c.inU32Subset && t.inU32Subset && e.inU32Subset
  | .while_ c b => c.inU32Subset && b.inU32Subset
  | _ => false

/-- A well-typed body whose variables and expressions are all `uint32_t` or `bool`. -/
def WellTypedU32 (Γ : CDecls) (s : MicroCStmt) : Prop :=
  WellTyped Γ s ∧ (∀ p ∈ Γ, p.2 ≠ .i64) ∧ s.inU32Subset = true

instance (Γ : CDecls) (s : MicroCStmt) : Decidable (WellTypedU32 Γ s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## Printing -/

/-- What follows the name in a declaration: ` = 0u; (void)x;` and a newline. The cast to void
    marks the variable used, so `-Wall -Werror` accepts a variable the body only writes. -/
def declTail (x : String) (t : CType) : String :=
  " = " ++ microCExprToString t.zero ++ "; (void)" ++ x ++ ";\n"

def declToString (d : String × CType) : String :=
  d.2.name ++ " " ++ d.1 ++ declTail d.1 d.2

def declsToString : CDecls → String
  | [] => ""
  | d :: ds => declToString d ++ declsToString ds

/-- The declarations, then the body as a compound statement. -/
def printTyped (Γ : CDecls) (s : MicroCStmt) : String :=
  declsToString Γ ++ "{ " ++ microCToString s ++ " }"

end TrustLean
