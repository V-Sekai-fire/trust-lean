/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/EvalWith.lean: the MicroC evaluator over an operator semantics

  `evalMicroCExprWith S` and `evalMicroCWith S` are `evalMicroCExpr` and `evalMicroC` with the
  operators of `S`. Each MicroC evaluator is one instance: `evalMicroC` is `.int`,
  `evalMicroC_uint32` is `.u32`, `evalMicroC_uint64` is `.u64` and `evalMicroC_int64` is `.i64`.
  `S.core` is the same semantics on Core operators, which `stmtToMicroC` translates.
-/

import TrustLean.MicroC.UnsignedEval
import TrustLean.MicroC.Int64Eval
import TrustLean.Core.EvalWith

set_option autoImplicit false

namespace TrustLean

/-- What a MicroC evaluator does at an operator and at `power`; the rest is shared. -/
structure MicroCOps where
  binOp : MicroCBinOp → Value → Value → Option Value
  unaryOp : MicroCUnaryOp → Value → Option Value
  pow : Int → Nat → Option Value

def MicroCOps.int : MicroCOps :=
  ⟨evalMicroCBinOp, evalMicroCUnaryOp, fun i n => some (.int (i ^ n))⟩

def MicroCOps.u32 : MicroCOps :=
  ⟨evalMicroCBinOp_uint32, evalMicroCUnaryOp_uint32, fun i n => some (.int (wrapUInt32 (i ^ n)))⟩

def MicroCOps.u64 : MicroCOps :=
  ⟨evalMicroCBinOp_uint64, evalMicroCUnaryOp_uint64, fun i n => some (.int (wrapUInt64 (i ^ n)))⟩

def MicroCOps.i64 : MicroCOps :=
  ⟨evalMicroCBinOp_int64, evalMicroCUnaryOp_int64, fun i n => some (.int (wrapInt64 (i ^ n)))⟩

/-- The same operators on the Core IR, through `binOpToMicroC` and `unaryOpToMicroC`. -/
def MicroCOps.core (S : MicroCOps) : CoreOps :=
  ⟨fun op => S.binOp (binOpToMicroC op), fun op => S.unaryOp (unaryOpToMicroC op), S.pow⟩

theorem MicroCOps.int_core : MicroCOps.int.core = CoreOps.int := by
  simp only [MicroCOps.core, MicroCOps.int, CoreOps.int, CoreOps.mk.injEq, and_true]
  constructor
  · funext op; cases op <;> rfl
  · funext op; cases op <;> rfl

/-! ## Evaluator -/

def evalMicroCExprWith (S : MicroCOps) (env : MicroCEnv) : MicroCExpr → Option Value
  | .litInt n => some (.int n)
  | .litU32 n => some (.int n.toNat)
  | .litBool b => some (.bool b)
  | .varRef name => some (env name)
  | .binOp op e1 e2 =>
    match evalMicroCExprWith S env e1, evalMicroCExprWith S env e2 with
    | some v1, some v2 => S.binOp op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match evalMicroCExprWith S env e with
    | some v => S.unaryOp op v
    | none => none
  | .powCall base n =>
    match evalMicroCExprWith S env base with
    | some (.int i) => S.pow i n
    | _ => none
  | .arrayAccess base idx =>
    match getMicroCArrayName base, evalMicroCExprWith S env idx with
    | some name, some (.int i) => some (env (name ++ "[" ++ toString i ++ "]"))
    | _, _ => none

def evalMicroCWith (S : MicroCOps) (fuel : Nat) (env : MicroCEnv) (stmt : MicroCStmt) :
    Option (Outcome × MicroCEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalMicroCExprWith S env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalMicroCExprWith S env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getMicroCArrayName base, evalMicroCExprWith S env idx, evalMicroCExprWith S env val with
    | some name, some (.int i), some v =>
      some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
    | _, _, _ => none
  | .load var base idx =>
    match getMicroCArrayName base, evalMicroCExprWith S env idx with
    | some name, some (.int i) =>
      some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
    | _, _ => none
  | .call _ _ _ => none
  | .seq s1 s2 =>
    match evalMicroCWith S fuel env s1 with
    | some (.normal, env') => evalMicroCWith S fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalMicroCExprWith S env cond with
    | some (.bool true) => evalMicroCWith S fuel env thenB
    | some (.bool false) => evalMicroCWith S fuel env elseB
    | _ => none
  | .while_ cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalMicroCExprWith S env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroCWith S fuel' env body with
        | some (.normal, env') => evalMicroCWith S fuel' env' (.while_ cond body)
        | some (.continue_, env') => evalMicroCWith S fuel' env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
termination_by (fuel, sizeOf stmt)

/-! ## Equation Lemmas -/

section
variable (S : MicroCOps) (fuel : Nat) (env : MicroCEnv)

@[simp] theorem evalMicroCWith_skip : evalMicroCWith S fuel env .skip = some (.normal, env) := by
  simp [evalMicroCWith]

@[simp] theorem evalMicroCWith_break :
    evalMicroCWith S fuel env .break_ = some (.break_, env) := by
  simp [evalMicroCWith]

@[simp] theorem evalMicroCWith_continue :
    evalMicroCWith S fuel env .continue_ = some (.continue_, env) := by
  simp [evalMicroCWith]

@[simp] theorem evalMicroCWith_return_none :
    evalMicroCWith S fuel env (.return_ none) = some (.return_ none, env) := by
  simp [evalMicroCWith]

@[simp] theorem evalMicroCWith_return_some (e : MicroCExpr) :
    evalMicroCWith S fuel env (.return_ (some e)) =
      match evalMicroCExprWith S env e with
      | some v => some (.return_ (some v), env)
      | none => none := by
  simp [evalMicroCWith]

@[simp] theorem evalMicroCWith_assign (name : String) (expr : MicroCExpr) :
    evalMicroCWith S fuel env (.assign name expr) =
      match evalMicroCExprWith S env expr with
      | some v => some (.normal, env.update name v)
      | none => none := by
  simp [evalMicroCWith]

@[simp] theorem evalMicroCWith_seq (s1 s2 : MicroCStmt) :
    evalMicroCWith S fuel env (.seq s1 s2) =
      match evalMicroCWith S fuel env s1 with
      | some (.normal, env') => evalMicroCWith S fuel env' s2
      | other => other := by
  simp [evalMicroCWith]

@[simp] theorem evalMicroCWith_ite (cond : MicroCExpr) (thenB elseB : MicroCStmt) :
    evalMicroCWith S fuel env (.ite cond thenB elseB) =
      match evalMicroCExprWith S env cond with
      | some (.bool true) => evalMicroCWith S fuel env thenB
      | some (.bool false) => evalMicroCWith S fuel env elseB
      | _ => none := by
  simp [evalMicroCWith]

@[simp] theorem evalMicroCWith_while_zero (cond : MicroCExpr) (body : MicroCStmt) :
    evalMicroCWith S 0 env (.while_ cond body) = some (.outOfFuel, env) := by
  simp [evalMicroCWith]

@[simp] theorem evalMicroCWith_while_succ (cond : MicroCExpr) (body : MicroCStmt) :
    evalMicroCWith S (fuel + 1) env (.while_ cond body) =
      match evalMicroCExprWith S env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroCWith S fuel env body with
        | some (.normal, env') => evalMicroCWith S fuel env' (.while_ cond body)
        | some (.continue_, env') => evalMicroCWith S fuel env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none := by
  simp [evalMicroCWith]

end

/-! ## Each Evaluator Is an Instance

`evalMicroCStep S rec` is one unfolding of `evalMicroCWith S` with `rec` for its recursive calls.
Two functions that both unfold this way agree everywhere, so an evaluator whose definition
unfolds to `evalMicroCStep S` of itself is `evalMicroCWith S`. -/

abbrev MicroCRun := Nat → MicroCEnv → MicroCStmt → Option (Outcome × MicroCEnv)

def evalMicroCStep (S : MicroCOps) (rec : MicroCRun) (fuel : Nat) (env : MicroCEnv) :
    MicroCStmt → Option (Outcome × MicroCEnv)
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalMicroCExprWith S env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalMicroCExprWith S env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getMicroCArrayName base, evalMicroCExprWith S env idx, evalMicroCExprWith S env val with
    | some name, some (.int i), some v =>
      some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
    | _, _, _ => none
  | .load var base idx =>
    match getMicroCArrayName base, evalMicroCExprWith S env idx with
    | some name, some (.int i) =>
      some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
    | _, _ => none
  | .call _ _ _ => none
  | .seq s1 s2 =>
    match rec fuel env s1 with
    | some (.normal, env') => rec fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalMicroCExprWith S env cond with
    | some (.bool true) => rec fuel env thenB
    | some (.bool false) => rec fuel env elseB
    | _ => none
  | .while_ cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalMicroCExprWith S env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match rec fuel' env body with
        | some (.normal, env') => rec fuel' env' (.while_ cond body)
        | some (.continue_, env') => rec fuel' env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none

theorem evalMicroCStep_unique (S : MicroCOps) (f g : MicroCRun)
    (hf : ∀ fuel env s, f fuel env s = evalMicroCStep S f fuel env s)
    (hg : ∀ fuel env s, g fuel env s = evalMicroCStep S g fuel env s) (fuel : Nat) :
    ∀ (env : MicroCEnv) (s : MicroCStmt), f fuel env s = g fuel env s := by
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihf =>
    intro env s
    induction s generalizing env with
    | seq s1 s2 ih1 ih2 =>
      rw [hf, hg]; simp only [evalMicroCStep, ih1 env, ih2]
    | ite c t e iht ihe =>
      rw [hf, hg]; simp only [evalMicroCStep, iht env, ihe env]
    | while_ c b _ =>
      rw [hf, hg]
      cases fuel with
      | zero => rfl
      | succ n => simp only [evalMicroCStep, ihf n (Nat.lt_succ_self n)]
    | _ => rw [hf, hg]; rfl

theorem evalMicroCWith_eq_step (S : MicroCOps) (fuel : Nat) (env : MicroCEnv) (s : MicroCStmt) :
    evalMicroCWith S fuel env s = evalMicroCStep S (evalMicroCWith S) fuel env s := by
  rw [evalMicroCWith.eq_def]; cases s <;> rfl

theorem evalMicroCExpr_eq_with (env : MicroCEnv) (e : MicroCExpr) :
    evalMicroCExpr env e = evalMicroCExprWith .int env e := by
  induction e with
  | binOp op e1 e2 ih1 ih2 => simp only [evalMicroCExpr, evalMicroCExprWith, ih1, ih2]; rfl
  | unaryOp op e ih => simp only [evalMicroCExpr, evalMicroCExprWith, ih]; rfl
  | powCall base n ih => simp only [evalMicroCExpr, evalMicroCExprWith, ih]; rfl
  | arrayAccess base idx _ ih => simp only [evalMicroCExpr, evalMicroCExprWith, ih]; rfl
  | _ => rfl

theorem evalMicroCExpr_uint32_eq_with (env : MicroCEnv) (e : MicroCExpr) :
    evalMicroCExpr_uint32 env e = evalMicroCExprWith .u32 env e := by
  induction e with
  | binOp op e1 e2 ih1 ih2 => simp only [evalMicroCExpr_uint32, evalMicroCExprWith, ih1, ih2]; rfl
  | unaryOp op e ih => simp only [evalMicroCExpr_uint32, evalMicroCExprWith, ih]; rfl
  | powCall base n ih => simp only [evalMicroCExpr_uint32, evalMicroCExprWith, ih]; rfl
  | arrayAccess base idx _ ih =>
    simp only [evalMicroCExpr_uint32, evalMicroCExprWith, ih]
    cases base <;> try rfl
    rcases evalMicroCExprWith _ env idx with _ | (_ | _) <;> rfl
  | _ => rfl

theorem evalMicroCExpr_uint64_eq_with (env : MicroCEnv) (e : MicroCExpr) :
    evalMicroCExpr_uint64 env e = evalMicroCExprWith .u64 env e := by
  induction e with
  | binOp op e1 e2 ih1 ih2 => simp only [evalMicroCExpr_uint64, evalMicroCExprWith, ih1, ih2]; rfl
  | unaryOp op e ih => simp only [evalMicroCExpr_uint64, evalMicroCExprWith, ih]; rfl
  | powCall base n ih => simp only [evalMicroCExpr_uint64, evalMicroCExprWith, ih]; rfl
  | arrayAccess base idx _ ih =>
    simp only [evalMicroCExpr_uint64, evalMicroCExprWith, ih]
    cases base <;> try rfl
    rcases evalMicroCExprWith _ env idx with _ | (_ | _) <;> rfl
  | _ => rfl

theorem evalMicroCExpr_int64_eq_with (env : MicroCEnv) (e : MicroCExpr) :
    evalMicroCExpr_int64 env e = evalMicroCExprWith .i64 env e := by
  induction e with
  | binOp op e1 e2 ih1 ih2 => simp only [evalMicroCExpr_int64, evalMicroCExprWith, ih1, ih2]; rfl
  | unaryOp op e ih => simp only [evalMicroCExpr_int64, evalMicroCExprWith, ih]; rfl
  | powCall base n ih => simp only [evalMicroCExpr_int64, evalMicroCExprWith, ih]; rfl
  | arrayAccess base idx _ ih => simp only [evalMicroCExpr_int64, evalMicroCExprWith, ih]; rfl
  | _ => rfl

theorem evalMicroC_eq_with (fuel : Nat) (env : MicroCEnv) (s : MicroCStmt) :
    evalMicroC fuel env s = evalMicroCWith .int fuel env s :=
  evalMicroCStep_unique .int _ _
    (fun fuel env s => by
      rw [evalMicroC.eq_def]; cases s <;> simp only [evalMicroCStep, evalMicroCExpr_eq_with] <;> rfl)
    (evalMicroCWith_eq_step .int) fuel env s

theorem evalMicroC_uint32_eq_with (fuel : Nat) (env : MicroCEnv) (s : MicroCStmt) :
    evalMicroC_uint32 fuel env s = evalMicroCWith .u32 fuel env s :=
  evalMicroCStep_unique .u32 _ _
    (fun fuel env s => by
      rw [evalMicroC_uint32.eq_def]
      cases s <;> simp only [evalMicroCStep, evalMicroCExpr_uint32_eq_with] <;> rfl)
    (evalMicroCWith_eq_step .u32) fuel env s

theorem evalMicroC_uint64_eq_with (fuel : Nat) (env : MicroCEnv) (s : MicroCStmt) :
    evalMicroC_uint64 fuel env s = evalMicroCWith .u64 fuel env s :=
  evalMicroCStep_unique .u64 _ _
    (fun fuel env s => by
      rw [evalMicroC_uint64.eq_def]
      cases s <;> simp only [evalMicroCStep, evalMicroCExpr_uint64_eq_with] <;> rfl)
    (evalMicroCWith_eq_step .u64) fuel env s

theorem evalMicroC_int64_eq_with (fuel : Nat) (env : MicroCEnv) (s : MicroCStmt) :
    evalMicroC_int64 fuel env s = evalMicroCWith .i64 fuel env s :=
  evalMicroCStep_unique .i64 _ _
    (fun fuel env s => by
      rw [evalMicroC_int64.eq_def]
      cases s <;> simp only [evalMicroCStep, evalMicroCExpr_int64_eq_with] <;> rfl)
    (evalMicroCWith_eq_step .i64) fuel env s

end TrustLean
