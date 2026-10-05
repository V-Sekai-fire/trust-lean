/-
  Trust-Lean — Verified Code Generation Framework
  Core/EvalWith.lean: the Core evaluator over an operator semantics

  `evalExprWith C` and `evalStmtWith C` are `evalExpr` and `evalStmt` with the operators of `C`.
  `CoreOps.int` gives back `evalExpr` and `evalStmt`.
-/

import TrustLean.Core.Eval

set_option autoImplicit false

namespace TrustLean

/-- What an evaluator does at an operator and at `power`; the rest of evaluation is shared. -/
structure CoreOps where
  binOp : BinOp → Value → Value → Option Value
  unaryOp : UnaryOp → Value → Option Value
  pow : Int → Nat → Option Value

/-- Unbounded integers: the operators of `evalExpr`. -/
def CoreOps.int : CoreOps := ⟨evalBinOp, evalUnaryOp, fun i n => some (.int (i ^ n))⟩

def evalExprWith (C : CoreOps) (env : LowLevelEnv) : LowLevelExpr → Option Value
  | .litInt n => some (.int n)
  | .litBool b => some (.bool b)
  | .varRef name => some (env name)
  | .binOp op e1 e2 =>
    match evalExprWith C env e1, evalExprWith C env e2 with
    | some v1, some v2 => C.binOp op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match evalExprWith C env e with
    | some v => C.unaryOp op v
    | none => none
  | .powCall base n =>
    match evalExprWith C env base with
    | some (.int i) => C.pow i n
    | _ => none
  | .addrOf v => some (env v)

def evalStmtWith (C : CoreOps) (fuel : Nat) (env : LowLevelEnv) (stmt : Stmt) :
    Option (Outcome × LowLevelEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalExprWith C env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalExprWith C env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getArrayName base, evalExprWith C env idx, evalExprWith C env val with
    | some name, some (.int i), some v => some (.normal, env.update (.array name i) v)
    | _, _, _ => none
  | .load var base idx =>
    match getArrayName base, evalExprWith C env idx with
    | some name, some (.int i) => some (.normal, env.update var (env (.array name i)))
    | _, _ => none
  | .call _ _ _ => none
  | .seq s1 s2 =>
    match evalStmtWith C fuel env s1 with
    | some (.normal, env') => evalStmtWith C fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalExprWith C env cond with
    | some (.bool true) => evalStmtWith C fuel env thenB
    | some (.bool false) => evalStmtWith C fuel env elseB
    | _ => none
  | .while cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalExprWith C env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalStmtWith C fuel' env body with
        | some (.normal, env') => evalStmtWith C fuel' env' (.while cond body)
        | some (.continue_, env') => evalStmtWith C fuel' env' (.while cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
  | .for_ init cond step body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalStmtWith C fuel' env init with
      | some (.normal, env') => evalStmtWith C fuel' env' (.while cond (.seq body step))
      | some (o, env') => some (o, env')
      | none => none
termination_by (fuel, sizeOf stmt)

/-! ## Equation Lemmas -/

section
variable (C : CoreOps) (fuel : Nat) (env : LowLevelEnv)

@[simp] theorem evalStmtWith_skip : evalStmtWith C fuel env .skip = some (.normal, env) := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_break : evalStmtWith C fuel env .break_ = some (.break_, env) := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_continue :
    evalStmtWith C fuel env .continue_ = some (.continue_, env) := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_return_none :
    evalStmtWith C fuel env (.return_ none) = some (.return_ none, env) := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_return_some (e : LowLevelExpr) :
    evalStmtWith C fuel env (.return_ (some e)) =
      match evalExprWith C env e with
      | some v => some (.return_ (some v), env)
      | none => none := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_assign (name : VarName) (expr : LowLevelExpr) :
    evalStmtWith C fuel env (.assign name expr) =
      match evalExprWith C env expr with
      | some v => some (.normal, env.update name v)
      | none => none := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_store (base idx val : LowLevelExpr) :
    evalStmtWith C fuel env (.store base idx val) =
      match getArrayName base, evalExprWith C env idx, evalExprWith C env val with
      | some name, some (.int i), some v => some (.normal, env.update (.array name i) v)
      | _, _, _ => none := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_load (var : VarName) (base idx : LowLevelExpr) :
    evalStmtWith C fuel env (.load var base idx) =
      match getArrayName base, evalExprWith C env idx with
      | some name, some (.int i) => some (.normal, env.update var (env (.array name i)))
      | _, _ => none := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_call (var : VarName) (fname : String) (args : List LowLevelExpr) :
    evalStmtWith C fuel env (.call var fname args) = none := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_seq (s1 s2 : Stmt) :
    evalStmtWith C fuel env (.seq s1 s2) =
      match evalStmtWith C fuel env s1 with
      | some (.normal, env') => evalStmtWith C fuel env' s2
      | other => other := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_ite (cond : LowLevelExpr) (thenB elseB : Stmt) :
    evalStmtWith C fuel env (.ite cond thenB elseB) =
      match evalExprWith C env cond with
      | some (.bool true) => evalStmtWith C fuel env thenB
      | some (.bool false) => evalStmtWith C fuel env elseB
      | _ => none := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_while_zero (cond : LowLevelExpr) (body : Stmt) :
    evalStmtWith C 0 env (.while cond body) = some (.outOfFuel, env) := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_while_succ (cond : LowLevelExpr) (body : Stmt) :
    evalStmtWith C (fuel + 1) env (.while cond body) =
      match evalExprWith C env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalStmtWith C fuel env body with
        | some (.normal, env') => evalStmtWith C fuel env' (.while cond body)
        | some (.continue_, env') => evalStmtWith C fuel env' (.while cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_for_zero (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) :
    evalStmtWith C 0 env (.for_ init cond step body) = some (.outOfFuel, env) := by
  simp [evalStmtWith]

@[simp] theorem evalStmtWith_for_succ (init : Stmt) (cond : LowLevelExpr) (step body : Stmt) :
    evalStmtWith C (fuel + 1) env (.for_ init cond step body) =
      match evalStmtWith C fuel env init with
      | some (.normal, env') => evalStmtWith C fuel env' (.while cond (.seq body step))
      | some (o, env') => some (o, env')
      | none => none := by
  simp [evalStmtWith]

end

/-! ## `CoreOps.int` Is `evalExpr` and `evalStmt` -/

theorem evalExpr_eq_with (env : LowLevelEnv) (e : LowLevelExpr) :
    evalExpr env e = evalExprWith .int env e := by
  induction e with
  | binOp op e1 e2 ih1 ih2 => simp only [evalExpr, evalExprWith, ih1, ih2]; rfl
  | unaryOp op e ih => simp only [evalExpr, evalExprWith, ih]; rfl
  | powCall base n ih => simp only [evalExpr, evalExprWith, ih]; rfl
  | _ => rfl

private theorem evalStmt_eq_with_step (fuel : Nat)
    (ihf : ∀ n < fuel, ∀ (s : Stmt) (env : LowLevelEnv),
      evalStmt n env s = evalStmtWith .int n env s) :
    ∀ (s : Stmt) (env : LowLevelEnv), evalStmt fuel env s = evalStmtWith .int fuel env s := by
  intro s
  induction s with
  | seq s1 s2 ih1 ih2 =>
    intro env
    simp only [evalStmt_seq, evalStmtWith_seq, ih1 env, ih2]; rfl
  | ite c t e iht ihe =>
    intro env
    simp only [evalStmt_ite, evalStmtWith_ite, evalExpr_eq_with, iht env, ihe env]; rfl
  | «while» c b _ =>
    intro env
    cases fuel with
    | zero => simp
    | succ n =>
      simp only [evalStmt_while_succ, evalStmtWith_while_succ, evalExpr_eq_with,
        ihf n (Nat.lt_succ_self n)]; rfl
  | for_ init c step b _ _ _ =>
    intro env
    cases fuel with
    | zero => simp
    | succ n =>
      simp only [evalStmt_for_succ, evalStmtWith_for_succ, ihf n (Nat.lt_succ_self n)]; rfl
  | _ =>
    intro env
    rw [evalStmt.eq_def, evalStmtWith.eq_def]
    try simp only [evalExpr_eq_with]
    try rfl

theorem evalStmt_eq_with (fuel : Nat) (env : LowLevelEnv) (s : Stmt) :
    evalStmt fuel env s = evalStmtWith .int fuel env s :=
  Nat.strong_induction_on (p := fun fuel => ∀ (s : Stmt) (env : LowLevelEnv),
      evalStmt fuel env s = evalStmtWith .int fuel env s) fuel
    (fun fuel ihf => evalStmt_eq_with_step fuel ihf) s env

end TrustLean
