/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/FuncEval.lean: running a function on its arguments

  `evalFunc_u32` runs a function on `uint32_t`, `bool` and buffer arguments with
  `evalMicroC_uint32`'s operators, and keeps each cell `p[i]` under the key `evalMicroC_uint32`
  gives it. A buffer is as long as its argument; reading or writing `p[i]` outside it is `none`
  (C11 6.5.6p8). `evalFunc_u32_eq_evalFuncS32` equates it with `evalFuncS32`, which runs the body
  on Lean's `UInt32` as `evalS32` does, under the same bounds.
-/

import TrustLean.MicroC.Func
import TrustLean.MicroC.UnsignedSimulation

set_option autoImplicit false

namespace TrustLean

/-! ## Bounds -/

/-- The length of each buffer; `none` for a name that is not a buffer. -/
abbrev Bounds := String → Option Nat

def Bounds.has (B : Bounds) (name : String) (i : Int) : Bool :=
  match B name with
  | some n => decide (0 ≤ i ∧ i < n)
  | none => false

/-! ## On `Value` -/

def evalMicroCExprB_uint32 (B : Bounds) (env : MicroCEnv) : MicroCExpr → Option Value
  | .litInt n => some (.int n)
  | .litU32 n => some (.int n.toNat)
  | .litBool b => some (.bool b)
  | .varRef name => some (env name)
  | .binOp op lhs rhs =>
    match evalMicroCExprB_uint32 B env lhs, evalMicroCExprB_uint32 B env rhs with
    | some v1, some v2 => evalMicroCBinOp_uint32 op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match evalMicroCExprB_uint32 B env e with
    | some v => evalMicroCUnaryOp_uint32 op v
    | none => none
  | .powCall base n =>
    match evalMicroCExprB_uint32 B env base with
    | some (.int i) => some (.int (wrapUInt32 (i ^ n)))
    | _ => none
  | .arrayAccess base idx =>
    match base with
    | .varRef name =>
      match evalMicroCExprB_uint32 B env idx with
      | some (.int i) =>
        if B.has name i then some (env (name ++ "[" ++ toString i ++ "]")) else none
      | _ => none
    | _ => none

/-- `evalMicroC_uint32` with every cell access checked against `B`. -/
def evalMicroCB_uint32 (B : Bounds) (fuel : Nat) (env : MicroCEnv) (stmt : MicroCStmt) :
    Option (Outcome × MicroCEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .return_ re =>
    match re with
    | some e =>
      match evalMicroCExprB_uint32 B env e with
      | some v => some (.return_ (some v), env)
      | none => none
    | none => some (.return_ none, env)
  | .assign name expr =>
    match evalMicroCExprB_uint32 B env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .store base idx val =>
    match getMicroCArrayName' base, evalMicroCExprB_uint32 B env idx,
      evalMicroCExprB_uint32 B env val with
    | some name, some (.int i), some v =>
      if B.has name i then some (.normal, env.update (name ++ "[" ++ toString i ++ "]") v)
      else none
    | _, _, _ => none
  | .load var base idx =>
    match getMicroCArrayName' base, evalMicroCExprB_uint32 B env idx with
    | some name, some (.int i) =>
      if B.has name i then some (.normal, env.update var (env (name ++ "[" ++ toString i ++ "]")))
      else none
    | _, _ => none
  | .call _ _ _ => none
  | .seq s1 s2 =>
    match evalMicroCB_uint32 B fuel env s1 with
    | some (.normal, env') => evalMicroCB_uint32 B fuel env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalMicroCExprB_uint32 B env cond with
    | some (.bool true) => evalMicroCB_uint32 B fuel env thenB
    | some (.bool false) => evalMicroCB_uint32 B fuel env elseB
    | _ => none
  | .while_ cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalMicroCExprB_uint32 B env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalMicroCB_uint32 B fuel' env body with
        | some (.normal, env') => evalMicroCB_uint32 B fuel' env' (.while_ cond body)
        | some (.continue_, env') => evalMicroCB_uint32 B fuel' env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
termination_by (fuel, sizeOf stmt)

/-! ## On `UInt32` -/

def evalS32BExpr (B : Bounds) (ρ : Store32) : MicroCExpr → Option V32
  | .litInt n => some (.w (UInt32.ofNat n.toNat))
  | .litU32 n => some (.w n)
  | .litBool b => some (.b b)
  | .varRef x => some (ρ x)
  | .binOp op l r =>
    match evalS32BExpr B ρ l, evalS32BExpr B ρ r with
    | some a, some b => binOpS32 op a b
    | _, _ => none
  | .unaryOp op e =>
    match evalS32BExpr B ρ e with
    | some a => unaryOpS32 op a
    | none => none
  | .powCall _ _ => none
  | .arrayAccess base idx =>
    match base with
    | .varRef name =>
      match evalS32BExpr B ρ idx with
      | some (.w i) => if B.has name i.toNat then some (ρ (cell32 name i)) else none
      | _ => none
    | _ => none

/-- `evalS32At` with every cell access checked against `B`. -/
def evalS32BAt (B : Bounds) (loop : Option Run32) : Store32 → MicroCStmt →
    Option (Outcome32 × Store32)
  | ρ, .skip => some (.normal, ρ)
  | ρ, .break_ => some (.break_, ρ)
  | ρ, .continue_ => some (.continue_, ρ)
  | ρ, .return_ none => some (.return_ none, ρ)
  | ρ, .return_ (some e) =>
    match evalS32BExpr B ρ e with
    | some v => some (.return_ (some v), ρ)
    | none => none
  | ρ, .assign x e =>
    match evalS32BExpr B ρ e with
    | some v => some (.normal, ρ.update x v)
    | none => none
  | ρ, .store base idx val =>
    match getMicroCArrayName' base, evalS32BExpr B ρ idx, evalS32BExpr B ρ val with
    | some name, some (.w i), some v =>
      if B.has name i.toNat then some (.normal, ρ.update (cell32 name i) v) else none
    | _, _, _ => none
  | ρ, .load x base idx =>
    match getMicroCArrayName' base, evalS32BExpr B ρ idx with
    | some name, some (.w i) =>
      if B.has name i.toNat then some (.normal, ρ.update x (ρ (cell32 name i))) else none
    | _, _ => none
  | _, .call _ _ _ => none
  | ρ, .seq s1 s2 =>
    match evalS32BAt B loop ρ s1 with
    | some (.normal, ρ') => evalS32BAt B loop ρ' s2
    | other => other
  | ρ, .ite c t e =>
    match evalS32BExpr B ρ c with
    | some (.b true) => evalS32BAt B loop ρ t
    | some (.b false) => evalS32BAt B loop ρ e
    | _ => none
  | ρ, .while_ c body =>
    match loop with
    | none => some (.outOfFuel, ρ)
    | some run =>
      match evalS32BExpr B ρ c with
      | some (.b false) => some (.normal, ρ)
      | some (.b true) =>
        match run ρ body with
        | some (.normal, ρ') => run ρ' (.while_ c body)
        | some (.continue_, ρ') => run ρ' (.while_ c body)
        | some (.break_, ρ') => some (.normal, ρ')
        | some (.return_ v, ρ') => some (.return_ v, ρ')
        | some (.outOfFuel, ρ') => some (.outOfFuel, ρ')
        | none => none
      | _ => none

def evalS32B (B : Bounds) : Nat → Store32 → MicroCStmt → Option (Outcome32 × Store32)
  | 0 => evalS32BAt B none
  | n + 1 => evalS32BAt B (some (evalS32B B n))

/-! ## The Two Agree -/

theorem evalS32BExpr_lift (B : Bounds) (ρ : Store32) :
    ∀ (e : MicroCExpr), e.u32Ok = true →
      evalMicroCExprB_uint32 B (V32.lift ∘ ρ) e = (evalS32BExpr B ρ e).map V32.lift
  | .litInt n, h => by
    simp only [MicroCExpr.u32Ok, decide_eq_true_eq] at h
    simp only [evalMicroCExprB_uint32, evalS32BExpr, Option.map_some, V32.lift,
      UInt32.toNat_ofNat_of_lt' (show n.toNat < UInt32.size by simp only [UInt32.size]; omega)]
    congr 2; omega
  | .litU32 _, _ => rfl
  | .litBool _, _ => rfl
  | .varRef _, _ => rfl
  | .binOp op l r, h => by
    simp only [MicroCExpr.u32Ok, Bool.and_eq_true] at h
    simp only [evalMicroCExprB_uint32, evalS32BExpr, evalS32BExpr_lift B ρ l h.1,
      evalS32BExpr_lift B ρ r h.2]
    cases evalS32BExpr B ρ l <;> cases evalS32BExpr B ρ r <;> simp [binOpS32_lift]
  | .unaryOp op e, h => by
    have hop : op = .neg ∨ op = .lnot := by cases op <;> simp_all [MicroCExpr.u32Ok]
    have he : e.u32Ok = true := by rcases hop with rfl | rfl <;> simpa [MicroCExpr.u32Ok] using h
    simp only [evalMicroCExprB_uint32, evalS32BExpr, evalS32BExpr_lift B ρ e he]
    cases evalS32BExpr B ρ e <;> simp [unaryOpS32_lift _ _ hop]
  | .powCall _ _, h => by simp [MicroCExpr.u32Ok] at h
  | .arrayAccess base idx, h => by
    simp only [MicroCExpr.u32Ok] at h
    simp only [evalMicroCExprB_uint32, evalS32BExpr]
    cases base <;> try rfl
    simp only [evalS32BExpr_lift B ρ idx h]
    rcases evalS32BExpr B ρ idx with _ | _ | _ <;> try rfl
    simp only [Option.map_some, V32.lift_w]
    split <;> rfl

private def loopOfB (B : Bounds) : Nat → Option Run32
  | 0 => none
  | n + 1 => some (evalS32B B n)

private theorem evalS32B_eq_At (B : Bounds) (fuel : Nat) :
    evalS32B B fuel = evalS32BAt B (loopOfB B fuel) := by
  cases fuel <;> rfl

private theorem evalS32B_step (B : Bounds) (fuel : Nat)
    (ihf : ∀ n < fuel, ∀ (s : MicroCStmt) (ρ : Store32), s.u32Ok = true →
      evalMicroCB_uint32 B n (V32.lift ∘ ρ) s = (evalS32B B n ρ s).map liftResult) :
    ∀ (s : MicroCStmt) (ρ : Store32), s.u32Ok = true →
      evalMicroCB_uint32 B fuel (V32.lift ∘ ρ) s =
        (evalS32BAt B (loopOfB B fuel) ρ s).map liftResult := by
  intro s
  induction s with
  | skip | break_ | continue_ | call =>
    intro ρ _; simp [evalMicroCB_uint32, evalS32BAt, liftResult, Outcome32.lift]
  | return_ re =>
    intro ρ hs
    cases re with
    | none => simp [evalMicroCB_uint32, evalS32BAt, liftResult, Outcome32.lift]
    | some e =>
      simp only [MicroCStmt.u32Ok] at hs
      simp only [evalMicroCB_uint32, evalS32BAt, evalS32BExpr_lift B ρ e hs]
      cases evalS32BExpr B ρ e <;> simp [liftResult, Outcome32.lift]
  | assign x e =>
    intro ρ hs
    simp only [MicroCStmt.u32Ok] at hs
    simp only [evalMicroCB_uint32, evalS32BAt, evalS32BExpr_lift B ρ e hs]
    cases evalS32BExpr B ρ e <;> simp [liftResult, Outcome32.lift, lift_update]
  | store base idx val =>
    intro ρ hs
    simp only [MicroCStmt.u32Ok, Bool.and_eq_true] at hs
    simp only [evalMicroCB_uint32, evalS32BAt, evalS32BExpr_lift B ρ idx hs.1,
      evalS32BExpr_lift B ρ val hs.2]
    cases getMicroCArrayName' base <;> rcases evalS32BExpr B ρ idx with _ | _ | _ <;>
      cases evalS32BExpr B ρ val <;> try rfl
    simp only [Option.map_some, V32.lift_w]
    split <;> simp [liftResult, Outcome32.lift, lift_update, cell32]
  | load x base idx =>
    intro ρ hs
    simp only [MicroCStmt.u32Ok] at hs
    simp only [evalMicroCB_uint32, evalS32BAt, evalS32BExpr_lift B ρ idx hs]
    cases getMicroCArrayName' base <;> rcases evalS32BExpr B ρ idx with _ | _ | _ <;> try rfl
    simp only [Option.map_some, V32.lift_w]
    split <;> simp [liftResult, Outcome32.lift, lift_update, cell32]
  | seq s1 s2 ih1 ih2 =>
    intro ρ hs
    simp only [MicroCStmt.u32Ok, Bool.and_eq_true] at hs
    simp only [evalMicroCB_uint32, evalS32BAt, ih1 ρ hs.1]
    rcases evalS32BAt B (loopOfB B fuel) ρ s1 with _ | ⟨oc, ρ'⟩
    · rfl
    · cases oc <;> simp [liftResult, Outcome32.lift, ih2 ρ' hs.2]
  | ite c t e iht ihe =>
    intro ρ hs
    simp only [MicroCStmt.u32Ok, Bool.and_eq_true] at hs
    simp only [evalMicroCB_uint32, evalS32BAt, evalS32BExpr_lift B ρ c hs.1.1]
    rcases evalS32BExpr B ρ c with _ | _ | (_ | _)
    · rfl
    · rfl
    · exact ihe ρ hs.2
    · exact iht ρ hs.1.2
  | while_ c body _ =>
    intro ρ hs
    have hs' := hs
    simp only [MicroCStmt.u32Ok, Bool.and_eq_true] at hs'
    cases fuel with
    | zero => simp [evalMicroCB_uint32, evalS32BAt, loopOfB, liftResult, Outcome32.lift]
    | succ n =>
      have hb := ihf n (Nat.lt_succ_self n) body
      have hw := ihf n (Nat.lt_succ_self n) (.while_ c body)
      simp only [evalMicroCB_uint32, evalS32BAt, loopOfB, evalS32BExpr_lift B ρ c hs'.1]
      rcases evalS32BExpr B ρ c with _ | _ | (_ | _)
      · rfl
      · rfl
      · simp [V32.lift, liftResult, Outcome32.lift]
      · simp only [Option.map_some, V32.lift, hb ρ hs'.2]
        rcases evalS32B B n ρ body with _ | ⟨oc, ρ'⟩
        · rfl
        · cases oc <;> simp [liftResult, Outcome32.lift, hw ρ' hs]

/-- On `U32Subset`, the bounded `evalMicroCB_uint32` is the bounded `evalS32B`, at every fuel. -/
theorem evalMicroCB_uint32_eq_evalS32B (B : Bounds) (fuel : Nat) (ρ : Store32) (s : MicroCStmt)
    (hs : U32Subset s) :
    evalMicroCB_uint32 B fuel (V32.lift ∘ ρ) s = (evalS32B B fuel ρ s).map liftResult := by
  rw [evalS32B_eq_At]
  exact Nat.strong_induction_on (p := fun fuel => ∀ (s : MicroCStmt) (ρ : Store32),
      s.u32Ok = true → evalMicroCB_uint32 B fuel (V32.lift ∘ ρ) s =
        (evalS32BAt B (loopOfB B fuel) ρ s).map liftResult) fuel
    (fun fuel ihf => evalS32B_step B fuel fun n hn s ρ h => by
      rw [evalS32B_eq_At]; exact ihf n hn s ρ h) s ρ hs

/-! ## Calls -/

/-- A `uint32_t` or `bool` argument, or the cells of a buffer. -/
inductive Arg32 where
  | val : V32 → Arg32
  | buf : List UInt32 → Arg32
  deriving DecidableEq, Repr

def writeCells (ρ : Store32) (p : String) : Nat → List UInt32 → Store32
  | _, [] => ρ
  | i, c :: cs => writeCells (ρ.update (cell32 p (UInt32.ofNat i)) (.w c)) p (i + 1) cs

/-- The store and bounds a call starts from: each parameter holds its argument, the cells of a
    buffer parameter `p` are `p[0]`, `p[1]`, ..., and every other name holds 0. `none` when an
    argument does not fit its parameter. -/
def bindArgs : CDecls → List Arg32 → Option (Store32 × Bounds)
  | [], [] => some (fun _ => .w 0, fun _ => none)
  | (x, t) :: ps, a :: as =>
    match bindArgs ps as, t, a with
    | some (ρ, B), .u32, .val (.w n) => some (ρ.update x (.w n), B)
    | some (ρ, B), .bool, .val (.b c) => some (ρ.update x (.b c), B)
    | some (ρ, B), .ptrU32, .buf cells =>
      some (writeCells ρ x 0 cells, fun n => if n = x then some cells.length else B n)
    | _, _, _ => none
  | _, _ => none

def CType.zero32 : CType → V32
  | .bool => .b false
  | _ => .w 0

def declareLocals (ρ : Store32) : CDecls → Store32
  | [] => ρ
  | (x, t) :: ls => (declareLocals ρ ls).update x t.zero32

/-- The final cells of each buffer parameter, in order, read with `get`. -/
def readBufs {α : Type} (get : String → α) (params : CDecls) (B : Bounds) : List (List α) :=
  params.filterMap fun p =>
    if p.2 = .ptrU32 then (B p.1).map fun n =>
      (List.range n).map fun i => get (cell32 p.1 (UInt32.ofNat i))
    else none

/-- Runs `f` on `args` under `evalS32B`: the return value and each buffer's final cells, or
    `none` when the body does not reach `return e;`. -/
def evalFuncS32 (fuel : Nat) (f : MicroCFunc) (args : List Arg32) :
    Option (V32 × List (List V32)) :=
  match bindArgs f.params args with
  | some (ρ, B) =>
    match evalS32B B fuel (declareLocals ρ f.locals) f.body with
    | some (.return_ (some v), ρ') => some (v, readBufs ρ' f.params B)
    | _ => none
  | none => none

/-- Runs `f` on `args` under `evalMicroCB_uint32`, from the environment `bindArgs` gives. -/
def evalFunc_u32 (fuel : Nat) (f : MicroCFunc) (args : List Arg32) :
    Option (Value × List (List Value)) :=
  match bindArgs f.params args with
  | some (ρ, B) =>
    match evalMicroCB_uint32 B fuel (V32.lift ∘ declareLocals ρ f.locals) f.body with
    | some (.return_ (some v), env) => some (v, readBufs env f.params B)
    | _ => none
  | none => none

def liftCall (r : V32 × List (List V32)) : Value × List (List Value) :=
  (r.1.lift, r.2.map (·.map V32.lift))

private theorem readBufs_lift (ρ : Store32) (params : CDecls) (B : Bounds) :
    readBufs (V32.lift ∘ ρ) params B = (readBufs ρ params B).map (·.map V32.lift) := by
  unfold readBufs
  rw [List.map_filterMap]
  congr 1
  funext p
  split <;> simp [Option.map_map, Function.comp_def]

/-- A function whose body is in `U32Subset` computes on `Value` what it computes on `UInt32`:
    the same return value and buffer cells, and `none` at the same out-of-bounds access. -/
theorem evalFunc_u32_eq_evalFuncS32 (fuel : Nat) (f : MicroCFunc) (args : List Arg32)
    (h : U32Subset f.body) : evalFunc_u32 fuel f args = (evalFuncS32 fuel f args).map liftCall := by
  unfold evalFunc_u32 evalFuncS32
  cases bindArgs f.params args with
  | none => rfl
  | some p =>
    obtain ⟨ρ, B⟩ := p
    simp only []
    rw [evalMicroCB_uint32_eq_evalS32B B fuel _ f.body h]
    rcases evalS32B B fuel (declareLocals ρ f.locals) f.body with _ | ⟨oc, ρ'⟩
    · rfl
    · rcases oc with _ | _ | _ | (_ | v) | _ <;>
        simp [liftResult, Outcome32.lift, liftCall, readBufs_lift]

theorem MicroCStmt.u32Ok_of_exprs : ∀ (s : MicroCStmt),
    s.exprs.all (fun e => e.inU32Subset) = true → s.u32Ok = true
  | .assign _ e, h | .return_ (some e), h => by
    simp only [MicroCStmt.exprs, List.all_cons, List.all_nil, Bool.and_true] at h
    exact MicroCExpr.u32Ok_of_inU32Subset e h
  | .store _ i v, h => by
    simp only [MicroCStmt.exprs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h
    simp [MicroCStmt.u32Ok, MicroCExpr.u32Ok_of_inU32Subset i h.2.1,
      MicroCExpr.u32Ok_of_inU32Subset v h.2.2]
  | .load _ _ i, h => by
    simp only [MicroCStmt.exprs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h
    exact MicroCExpr.u32Ok_of_inU32Subset i h.2
  | .seq s1 s2, h => by
    simp only [MicroCStmt.exprs, List.all_append, Bool.and_eq_true] at h
    simp [MicroCStmt.u32Ok, u32Ok_of_exprs s1 h.1, u32Ok_of_exprs s2 h.2]
  | .ite c t e, h => by
    simp only [MicroCStmt.exprs, List.all_cons, List.all_append, Bool.and_eq_true] at h
    simp [MicroCStmt.u32Ok, MicroCExpr.u32Ok_of_inU32Subset c h.1, u32Ok_of_exprs t h.2.1,
      u32Ok_of_exprs e h.2.2]
  | .while_ c b, h => by
    simp only [MicroCStmt.exprs, List.all_cons, Bool.and_eq_true] at h
    simp [MicroCStmt.u32Ok, MicroCExpr.u32Ok_of_inU32Subset c h.1, u32Ok_of_exprs b h.2]
  | .skip, _ | .break_, _ | .continue_, _ | .return_ none, _ | .call _ _ _, _ => rfl

theorem WFFunc.u32Subset {f : MicroCFunc} (h : WFFunc f) : U32Subset f.body := by
  have := List.all_eq_true.mp h.2.2.2.2.2.2.2.2
  exact MicroCStmt.u32Ok_of_exprs f.body (List.all_eq_true.mpr fun e he => by
    have := this e he; simp only [Bool.and_eq_true] at this; exact this.1)

/-- **Function semantics**: a well-formed function computes on `Value` what it computes on
    `UInt32`. -/
theorem evalFunc_u32_correct (fuel : Nat) (f : MicroCFunc) (args : List Arg32) (h : WFFunc f) :
    evalFunc_u32 fuel f args = (evalFuncS32 fuel f args).map liftCall :=
  evalFunc_u32_eq_evalFuncS32 fuel f args h.u32Subset

/-! ## A Ring Buffer -/

private def v (x : String) : MicroCExpr := .varRef x
private def bin (op : MicroCBinOp) (l r : MicroCExpr) : MicroCExpr := .binOp op l r

/-- `occ = tail - head; if (mask < occ) return tail; buf[tail & mask] = v; return tail + 1u;`
    A full ring, whose occupancy is above `mask`, is left unchanged. -/
def ringPush : MicroCFunc where
  name := "ring_push"
  ret := .u32
  params := [("head", .u32), ("tail", .u32), ("mask", .u32), ("buf", .ptrU32), ("v", .u32)]
  locals := [("occ", .u32)]
  body :=
    .seq (.assign "occ" (bin .sub (v "tail") (v "head")))
      (.ite (bin .ltOp (v "mask") (v "occ"))
        (.return_ (some (v "tail")))
        (.seq (.store (v "buf") (bin .band (v "tail") (v "mask")) (v "v"))
          (.return_ (some (bin .add (v "tail") (.litU32 1))))))

/-- `if (tail == head) return head; x = buf[head & mask]; out[0u] = x; return head + 1u;` -/
def ringPop : MicroCFunc where
  name := "ring_pop"
  ret := .u32
  params := [("head", .u32), ("tail", .u32), ("mask", .u32), ("buf", .ptrU32), ("out", .ptrU32)]
  locals := [("x", .u32)]
  body :=
    .ite (bin .eqOp (v "tail") (v "head"))
      (.return_ (some (v "head")))
      (.seq (.load "x" (v "buf") (bin .band (v "head") (v "mask")))
        (.seq (.store (v "out") (.litU32 0) (v "x"))
          (.return_ (some (bin .add (v "head") (.litU32 1))))))

/-- `return (1u << bits) - 1u;`, undefined from `bits = 32` (C11 6.5.7p3). -/
def ringMask : MicroCFunc where
  name := "ring_mask"
  ret := .u32
  params := [("bits", .u32)]
  locals := []
  body := .return_ (some (bin .sub (bin .bshl (.litU32 1) (v "bits")) (.litU32 1)))

theorem ringPush_wf : WFFunc ringPush := by decide
theorem ringPop_wf : WFFunc ringPop := by decide
theorem ringMask_wf : WFFunc ringMask := by decide

theorem ringPush_roundtrip : parseMicroCFunc (microCFuncToString ringPush) = some ringPush :=
  master_func_roundtrip ringPush ringPush_wf

example : WFFile [ringPush, ringPop, ringMask] := by decide

/-- Two functions with one name. -/
example : ¬ WFFile [ringPush, ringPush] := by decide

/-- A path that ends without `return e;`, which `-Wreturn-type` rejects. -/
example : ¬ WFFunc { ringPush with body := .seq (.assign "occ" (v "tail")) .skip } := by decide

/-- A local of pointer type. -/
example : ¬ WFFunc { ringPush with locals := [("occ", .u32), ("p", .ptrU32)] } := by decide

/-- A store to a `uint32_t` parameter. -/
example : ¬ WFFunc { ringPop with
    body := .seq (.store (v "head") (.litU32 0) (v "tail")) (.return_ (some (v "head"))) } := by
  decide

/-- `bits + 1` with an unsuffixed literal, which is not `uint32_t` arithmetic. -/
example : ¬ WFFunc { ringMask with body := .return_ (some (bin .add (v "bits") (.litInt 1))) } := by
  decide

private def w (n : UInt32) : Arg32 := .val (.w n)

/-- At `tail = 2^32 - 1` the push stores to `buf[7]` and returns 0. -/
theorem evalFunc_u32_ringPush_wrap :
    evalFunc_u32 1 ringPush [w 4294967294, w 4294967295, w 7, .buf [0, 0, 0, 0, 0, 0, 0, 0], w 42] =
      some (.int 0, [[.int 0, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0, .int 42]]) := by
  rw [evalFunc_u32_correct 1 ringPush _ ringPush_wf]
  decide

/-- A full ring returns `tail` and leaves every cell as it was. -/
theorem evalFunc_u32_ringPush_full :
    evalFunc_u32 1 ringPush [w 4294967295, w 3, w 3, .buf [1, 2, 3, 4], w 42] =
      some (.int 3, [[.int 1, .int 2, .int 3, .int 4]]) := by
  rw [evalFunc_u32_correct 1 ringPush _ ringPush_wf]
  decide

/-- A buffer one cell short of `mask + 1`, so the push at `tail = 7` stores to `buf[7]`. -/
private def shortArgs : List Arg32 := [w 0, w 7, w 7, .buf [0, 0, 0, 0, 0, 0, 0], w 42]

theorem evalFunc_u32_ringPush_outOfBounds : evalFunc_u32 1 ringPush shortArgs = none := by
  rw [evalFunc_u32_correct 1 ringPush _ ringPush_wf]
  decide

/-- From the same arguments, `evalMicroC_uint32`, which has no bound, writes that cell and
    returns 8. -/
theorem evalMicroC_uint32_ringPush_outOfBounds :
    ∃ ρ B, bindArgs ringPush.params shortArgs = some (ρ, B) ∧
      (evalMicroC_uint32 1 (V32.lift ∘ declareLocals ρ ringPush.locals) ringPush.body).map (·.1) =
        some (.return_ (some (.int 8))) := by
  refine ⟨_, _, rfl, ?_⟩
  rw [evalMicroC_uint32_eq_evalS32 1 _ _ (by decide)]
  decide

end TrustLean
