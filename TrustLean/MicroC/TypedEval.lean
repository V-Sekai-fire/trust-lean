/-
  Trust-Lean — Verified Code Generation Framework
  MicroC/TypedEval.lean: the semantics of typed programs

  An operator acts on its operands' declared type: `int64_t` operations give `none` where C11
  is undefined and `uint32_t` operations wrap modulo 2^32. On the `uint32_t` subset this is
  `evalMicroC_uint32`, and on every well-typed program each variable keeps a value of its type.
-/

import TrustLean.MicroC.Typed
import TrustLean.MicroC.Int64Eval
import TrustLean.MicroC.UnsignedEval

set_option autoImplicit false

namespace TrustLean

/-! ## Evaluator -/

/-- A binary operator on operands of type `ty`: the `int64_t` semantics, or the `uint32_t` one,
    whose logical operators are those of every evaluator. -/
def tyBinOp (ty : Option (CType × Bool)) (op : MicroCBinOp) (v1 v2 : Value) : Option Value :=
  match ty with
  | some (.i64, _) => evalMicroCBinOp_int64 op v1 v2
  | _ => evalMicroCBinOp_uint32 op v1 v2

def tyUnaryOp (ty : Option (CType × Bool)) (op : MicroCUnaryOp) (v : Value) : Option Value :=
  match ty with
  | some (.i64, _) => evalMicroCUnaryOp_int64 op v
  | _ => evalMicroCUnaryOp_uint32 op v

/-- `power(i, n)` on `int64_t`: the exact power, or `none` when it overflows. -/
def powInt64 (i : Int) (n : Nat) : Option Value :=
  if InInt64Range (i ^ n) then some (.int (i ^ n)) else none

def evalTypedExpr (Γ : CDecls) (env : MicroCEnv) : MicroCExpr → Option Value
  | .litInt n => some (.int n)
  | .litU32 n => some (.int n.toNat)
  | .litBool b => some (.bool b)
  | .varRef x => some (env x)
  | .binOp op l r =>
    match evalTypedExpr Γ env l, evalTypedExpr Γ env r with
    | some v1, some v2 => tyBinOp (exprTy Γ l) op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match evalTypedExpr Γ env e with
    | some v => tyUnaryOp (exprTy Γ e) op v
    | none => none
  | .powCall b n =>
    match evalTypedExpr Γ env b with
    | some (.int i) => powInt64 i n
    | _ => none
  | .arrayAccess _ _ => none

/-- Evaluate a typed body. Arrays, calls and `return` are outside the typed subset. -/
def evalTyped (fuel : Nat) (Γ : CDecls) (env : MicroCEnv) (stmt : MicroCStmt) :
    Option (Outcome × MicroCEnv) :=
  match stmt with
  | .skip => some (.normal, env)
  | .break_ => some (.break_, env)
  | .continue_ => some (.continue_, env)
  | .assign name expr =>
    match evalTypedExpr Γ env expr with
    | some v => some (.normal, env.update name v)
    | none => none
  | .seq s1 s2 =>
    match evalTyped fuel Γ env s1 with
    | some (.normal, env') => evalTyped fuel Γ env' s2
    | other => other
  | .ite cond thenB elseB =>
    match evalTypedExpr Γ env cond with
    | some (.bool true) => evalTyped fuel Γ env thenB
    | some (.bool false) => evalTyped fuel Γ env elseB
    | _ => none
  | .while_ cond body =>
    match fuel with
    | 0 => some (.outOfFuel, env)
    | fuel' + 1 =>
      match evalTypedExpr Γ env cond with
      | some (.bool false) => some (.normal, env)
      | some (.bool true) =>
        match evalTyped fuel' Γ env body with
        | some (.normal, env') => evalTyped fuel' Γ env' (.while_ cond body)
        | some (.continue_, env') => evalTyped fuel' Γ env' (.while_ cond body)
        | some (.break_, env') => some (.normal, env')
        | some (.return_ rv, env') => some (.return_ rv, env')
        | some (.outOfFuel, env') => some (.outOfFuel, env')
        | none => none
      | _ => none
  | _ => none
termination_by (fuel, sizeOf stmt)

/-! ## The `uint32_t` Subset Is `evalMicroC_uint32` -/

theorem exprTy_ne_i64 (Γ : CDecls) (hΓ : ∀ p ∈ Γ, p.2 ≠ .i64) :
    ∀ (e : MicroCExpr), e.inU32Subset = true → ∀ v, exprTy Γ e ≠ some (.i64, v)
  | .litU32 _, _, _ => by simp [exprTy]
  | .litBool _, _, _ => by simp [exprTy]
  | .varRef x, _, v => by
    intro h
    simp only [exprTy, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨t, ht, rfl, -⟩ := h
    exact hΓ _ (lookup_mem ht) rfl
  | .binOp op l r, hs, v => by
    simp only [MicroCExpr.inU32Subset, Bool.and_eq_true] at hs
    intro h
    simp only [exprTy] at h
    split at h
    · rename_i tl vl tr vr hl hr
      split at h
      · cases tl with
        | i64 => exact exprTy_ne_i64 Γ hΓ l hs.1 vl hl
        | u32 => cases op <;> simp only [binOpTy] at h <;> (try split at h) <;> simp at h
        | bool => cases op <;> simp [binOpTy] at h
      · simp at h
    · simp at h
  | .unaryOp op e, hs, v => by
    intro h
    simp only [exprTy] at h
    split at h
    · rename_i t ve he
      split at h
      · simp at h
      · cases op with
        | neg =>
          simp only [MicroCExpr.inU32Subset] at hs
          cases t with
          | i64 => exact exprTy_ne_i64 Γ hΓ e hs ve he
          | u32 | bool => simp [unaryOpTy] at h
        | lnot => cases t <;> simp [unaryOpTy] at h
        | widen32to64 | trunc64to32 => simp [MicroCExpr.inU32Subset] at hs
    · simp at h
  | .litInt _, hs, _ => by simp [MicroCExpr.inU32Subset] at hs
  | .powCall _ _, hs, _ => by simp [MicroCExpr.inU32Subset] at hs
  | .arrayAccess _ _, hs, _ => by simp [MicroCExpr.inU32Subset] at hs

private theorem tyBinOp_of_ne_i64 {ty : Option (CType × Bool)} (h : ∀ v, ty ≠ some (.i64, v))
    (op : MicroCBinOp) (v1 v2 : Value) : tyBinOp ty op v1 v2 = evalMicroCBinOp_uint32 op v1 v2 := by
  unfold tyBinOp; split
  · rename_i v; exact absurd rfl (h v)
  · rfl

private theorem tyUnaryOp_of_ne_i64 {ty : Option (CType × Bool)} (h : ∀ v, ty ≠ some (.i64, v))
    (op : MicroCUnaryOp) (v : Value) : tyUnaryOp ty op v = evalMicroCUnaryOp_uint32 op v := by
  unfold tyUnaryOp; split
  · rename_i v; exact absurd rfl (h v)
  · rfl

theorem evalTypedExpr_eq_uint32 (Γ : CDecls) (hΓ : ∀ p ∈ Γ, p.2 ≠ .i64) (env : MicroCEnv) :
    ∀ (e : MicroCExpr), e.inU32Subset = true → evalTypedExpr Γ env e = evalMicroCExpr_uint32 env e
  | .litU32 _, _ => rfl
  | .litBool _, _ => rfl
  | .varRef _, _ => rfl
  | .binOp op l r, hs => by
    simp only [MicroCExpr.inU32Subset, Bool.and_eq_true] at hs
    simp only [evalTypedExpr, evalMicroCExpr_uint32,
      evalTypedExpr_eq_uint32 Γ hΓ env l hs.1, evalTypedExpr_eq_uint32 Γ hΓ env r hs.2,
      tyBinOp_of_ne_i64 (exprTy_ne_i64 Γ hΓ l hs.1)]
    rfl
  | .unaryOp op e, hs => by
    have he : e.inU32Subset = true := by
      cases op <;> simp_all [MicroCExpr.inU32Subset]
    simp only [evalTypedExpr, evalMicroCExpr_uint32, evalTypedExpr_eq_uint32 Γ hΓ env e he,
      tyUnaryOp_of_ne_i64 (exprTy_ne_i64 Γ hΓ e he)]
    rfl
  | .litInt _, hs => by simp [MicroCExpr.inU32Subset] at hs
  | .powCall _ _, hs => by simp [MicroCExpr.inU32Subset] at hs
  | .arrayAccess _ _, hs => by simp [MicroCExpr.inU32Subset] at hs

private theorem evalTyped_eq_uint32_step (Γ : CDecls) (hΓ : ∀ p ∈ Γ, p.2 ≠ .i64) (fuel : Nat)
    (ihf : ∀ fuel' < fuel, ∀ (s : MicroCStmt) (env : MicroCEnv), s.inU32Subset = true →
      evalTyped fuel' Γ env s = evalMicroC_uint32 fuel' env s) :
    ∀ (s : MicroCStmt) (env : MicroCEnv), s.inU32Subset = true →
      evalTyped fuel Γ env s = evalMicroC_uint32 fuel env s := by
  intro s
  induction s with
  | skip | break_ | continue_ => intro env _; simp [evalTyped, evalMicroC_uint32]
  | assign x e =>
    intro env hs
    simp only [MicroCStmt.inU32Subset] at hs
    simp only [evalTyped, evalMicroC_uint32, evalTypedExpr_eq_uint32 Γ hΓ env e hs]
    rfl
  | seq s1 s2 ih1 ih2 =>
    intro env hs
    simp only [MicroCStmt.inU32Subset, Bool.and_eq_true] at hs
    have h2 : ∀ env', evalTyped fuel Γ env' s2 = evalMicroC_uint32 fuel env' s2 :=
      fun env' => ih2 env' hs.2
    simp only [evalTyped, evalMicroC_uint32, ih1 env hs.1, h2]
    rfl
  | ite c t e iht ihe =>
    intro env hs
    simp only [MicroCStmt.inU32Subset, Bool.and_eq_true] at hs
    simp only [evalTyped, evalMicroC_uint32, evalTypedExpr_eq_uint32 Γ hΓ env c hs.1.1,
      iht env hs.1.2, ihe env hs.2]
    rfl
  | while_ c b ihb =>
    intro env hs
    have hs' := hs
    simp only [MicroCStmt.inU32Subset, Bool.and_eq_true] at hs'
    cases fuel with
    | zero => simp [evalTyped, evalMicroC_uint32]
    | succ n =>
      have hb : ∀ env', evalTyped n Γ env' b = evalMicroC_uint32 n env' b :=
        fun env' => ihf n (Nat.lt_succ_self n) b env' hs'.2
      have hw : ∀ env', evalTyped n Γ env' (.while_ c b) = evalMicroC_uint32 n env' (.while_ c b) :=
        fun env' => ihf n (Nat.lt_succ_self n) _ env' hs
      simp only [evalTyped, evalMicroC_uint32, evalTypedExpr_eq_uint32 Γ hΓ env c hs'.1, hb, hw]
      rfl
  | return_ _ => intro env hs; simp [MicroCStmt.inU32Subset] at hs
  | store _ _ _ => intro env hs; simp [MicroCStmt.inU32Subset] at hs
  | load _ _ _ => intro env hs; simp [MicroCStmt.inU32Subset] at hs
  | call _ _ _ => intro env hs; simp [MicroCStmt.inU32Subset] at hs

/-- On the `uint32_t` subset, the typed semantics is `evalMicroC_uint32`. -/
theorem evalTyped_eq_evalMicroC_uint32 (Γ : CDecls) (s : MicroCStmt) (h : WellTypedU32 Γ s)
    (fuel : Nat) (env : MicroCEnv) : evalTyped fuel Γ env s = evalMicroC_uint32 fuel env s :=
  Nat.strong_induction_on (p := fun fuel => ∀ (s : MicroCStmt) (env : MicroCEnv),
      s.inU32Subset = true → evalTyped fuel Γ env s = evalMicroC_uint32 fuel env s) fuel
    (fun fuel ihf => evalTyped_eq_uint32_step Γ h.2.1 fuel ihf) s env h.2.2

/-! ## Every Variable Keeps a Value of Its Type -/

/-- `v` is a value of C type `t`. -/
def CType.HasValue : CType → Value → Prop
  | .u32, .int n => 0 ≤ n ∧ n < 2 ^ 32
  | .i64, .int n => InInt64Range n
  | .bool, .bool _ => True
  | _, _ => False

/-- Every declared variable holds a value of its declared type. -/
def EnvTyped (Γ : CDecls) (env : MicroCEnv) : Prop :=
  ∀ x t, Γ.lookup x = some t → t.HasValue (env x)

theorem typedDefault_typed (Γ : CDecls) : EnvTyped Γ (typedDefault Γ) := by
  intro x t h
  simp only [typedDefault, h]
  cases t <;> simp [CType.HasValue, InInt64Range, minInt64, maxInt64]

theorem EnvTyped.update {Γ : CDecls} {env : MicroCEnv} {x : String} {t : CType} {v : Value}
    (henv : EnvTyped Γ env) (hx : Γ.lookup x = some t) (hv : t.HasValue v) :
    EnvTyped Γ (env.update x v) := by
  intro y u hy
  by_cases hyx : y = x
  · subst hyx; rw [hx] at hy; cases hy; simpa using hv
  · rw [MicroCEnv.update_other _ _ _ _ hyx]; exact henv y u hy

private theorem wrapUInt32_range (x : Int) : 0 ≤ wrapUInt32 x ∧ wrapUInt32 x < 2 ^ 32 :=
  ⟨wrapWidth_nonneg 32 x, wrapWidth_lt 32 x⟩

private theorem u32_inRange64 (x : Int) : InInt64Range (wrapUInt32 x) := by
  have := wrapUInt32_range x; unfold InInt64Range minInt64 maxInt64; omega

private theorem mod32_range (x : Int) : 0 ≤ x % (2 ^ 32 : Int) ∧ x % (2 ^ 32 : Int) < 2 ^ 32 :=
  ⟨Int.emod_nonneg x (by decide), Int.emod_lt_of_pos x (by decide)⟩

theorem binOp_typed (op : MicroCBinOp) (l r : MicroCExpr) (t : CType) (vl vr : Bool)
    (t' : CType) (r' : Bool) (hty : binOpTy op l r t vl vr = some (t', r'))
    (v1 v2 : Value) (h1 : t.HasValue v1) (h2 : t.HasValue v2) (v : Value)
    (hv : tyBinOp (some (t, vl)) op v1 v2 = some v) : t'.HasValue v := by
  cases t <;> cases v1 <;> cases v2 <;> simp only [CType.HasValue] at h1 h2 <;>
    simp only [tyBinOp] at hv <;> cases op <;> simp only [binOpTy] at hty <;>
    (try split at hty) <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hty <;>
    obtain ⟨rfl, -⟩ := hty <;> cases v <;> simp only [CType.HasValue] <;>
    first
    | trivial
    | exact evalMicroCBinOp_int64_inRange _ _ _ _ hv
    | (simp only [evalMicroCBinOp_uint32, Option.some.injEq, Value.int.injEq] at hv
       first
       | (subst hv; exact wrapUInt32_range _)
       | (split at hv
          · simp only [Option.some.injEq, Value.int.injEq] at hv; subst hv; exact wrapUInt32_range _
          · simp at hv))
    | simp [evalMicroCBinOp_uint32, evalMicroCBinOp_int64, Option.map_eq_some_iff] at hv

theorem unaryOp_typed (op : MicroCUnaryOp) (t : CType) (r : Bool) (t' : CType) (r' : Bool)
    (hty : unaryOpTy op t r = some (t', r')) (v1 : Value) (h1 : t.HasValue v1) (v : Value)
    (hv : tyUnaryOp (some (t, r)) op v1 = some v) : t'.HasValue v := by
  cases t <;> cases v1 <;> simp only [CType.HasValue] at h1 <;> simp only [tyUnaryOp] at hv <;>
    cases op <;> simp only [unaryOpTy, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hty <;>
    obtain ⟨rfl, -⟩ := hty <;> cases v <;> simp only [CType.HasValue] <;>
    first
    | trivial
    | exact evalMicroCUnaryOp_int64_inRange _ _ _ hv
    | (simp only [evalMicroCUnaryOp_uint32, evalMicroCUnaryOp_int64, Option.some.injEq,
        Value.int.injEq] at hv
       subst hv
       first
       | exact wrapUInt32_range _
       | exact mod32_range _
       | exact u32_inRange64 _)
    | simp [evalMicroCUnaryOp_uint32, evalMicroCUnaryOp_int64, Option.map_eq_some_iff] at hv

/-- An expression of type `t` evaluates to a value of type `t`. -/
theorem evalTypedExpr_typed (Γ : CDecls) (env : MicroCEnv) (henv : EnvTyped Γ env) :
    ∀ (e : MicroCExpr) (t : CType) (r : Bool) (v : Value), exprTy Γ e = some (t, r) →
      evalTypedExpr Γ env e = some v → t.HasValue v
  | .litInt n, t, r, v, hty, hv => by
    simp only [exprTy] at hty
    split at hty
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hty; obtain ⟨rfl, -⟩ := hty
      simp only [evalTypedExpr, Option.some.injEq] at hv; subst hv
      simp only [CType.HasValue, InInt64Range, minInt64, maxInt64] at hn ⊢; omega
    · simp at hty
  | .litU32 n, t, r, v, hty, hv => by
    simp only [exprTy, Option.some.injEq, Prod.mk.injEq] at hty; obtain ⟨rfl, -⟩ := hty
    simp only [evalTypedExpr, Option.some.injEq] at hv; subst hv
    simp only [CType.HasValue]; have := n.toNat_lt; omega
  | .litBool b, t, r, v, hty, hv => by
    simp only [exprTy, Option.some.injEq, Prod.mk.injEq] at hty; obtain ⟨rfl, -⟩ := hty
    simp only [evalTypedExpr, Option.some.injEq] at hv; subst hv; trivial
  | .varRef x, t, r, v, hty, hv => by
    simp only [exprTy, Option.map_eq_some_iff, Prod.mk.injEq] at hty
    obtain ⟨u, hu, rfl, -⟩ := hty
    simp only [evalTypedExpr, Option.some.injEq] at hv; subst hv; exact henv x u hu
  | .binOp op l r, t, rr, v, hty, hv => by
    simp only [exprTy] at hty
    split at hty
    · rename_i tl vl tr vr hl hr
      split at hty
      · rename_i htlr; subst htlr
        simp only [evalTypedExpr] at hv
        split at hv
        · rename_i v1 v2 h1 h2
          rw [hl] at hv
          exact binOp_typed op l r tl vl vr t rr hty v1 v2
            (evalTypedExpr_typed Γ env henv l tl vl v1 hl h1)
            (evalTypedExpr_typed Γ env henv r tl vr v2 hr h2) v hv
        · simp at hv
      · simp at hty
    · simp at hty
  | .unaryOp op e, t, rr, v, hty, hv => by
    simp only [exprTy] at hty
    split at hty
    · rename_i te ve he
      split at hty
      · simp at hty
      · simp only [evalTypedExpr] at hv
        split at hv
        · rename_i v1 h1
          rw [he] at hv
          exact unaryOp_typed op te ve t rr hty v1
            (evalTypedExpr_typed Γ env henv e te ve v1 he h1) v hv
        · simp at hv
    · simp at hty
  | .powCall b n, t, rr, v, hty, hv => by
    simp only [exprTy] at hty
    split at hty
    · split at hty
      · simp only [Option.some.injEq, Prod.mk.injEq] at hty; obtain ⟨rfl, -⟩ := hty
        simp only [evalTypedExpr] at hv
        split at hv
        · simp only [powInt64] at hv
          split at hv
          · rename_i hr; simp only [Option.some.injEq] at hv; subst hv; exact hr
          · simp at hv
        · simp at hv
      · simp at hty
    · simp at hty
  | .arrayAccess _ _, _, _, _, hty, _ => by simp [exprTy] at hty

private theorem binOp_defined (op : MicroCBinOp) (l r : MicroCExpr) (t : CType) (vl vr : Bool)
    (t' : CType) (r' : Bool) (hty : binOpTy op l r t vl vr = some (t', r'))
    (hop : binOpDefined op r t = true) (v1 v2 : Value) (h1 : t.HasValue v1) (h2 : t.HasValue v2)
    (hr : ∀ n, r = .litU32 n → v2 = .int n.toNat) :
    ∃ v, tyBinOp (some (t, vl)) op v1 v2 = some v := by
  cases t <;> cases v1 <;> cases v2 <;> simp only [CType.HasValue] at h1 h2 <;>
    cases op <;> simp only [binOpTy, binOpDefined, reduceCtorEq] at hty hop <;>
    simp [tyBinOp, evalMicroCBinOp_uint32, evalMicroCBinOp_int64]
  all_goals
    cases r <;> simp at hop
    rename_i n
    obtain rfl := Value.int.inj (hr n rfl)
    simp only [shiftCountOk, decide_eq_true_eq] at hty
    split at hty
    · omega
    · simp at hty

/-- A well-typed expression that is `definedOn Γ` has a value wherever each variable holds a
    value of its type. So `evalTyped`, which evaluates the right operand of `&&` and `||` that C
    may skip, gives `none` only where C evaluates an undefined operation. -/
theorem evalTypedExpr_definedOn (Γ : CDecls) (env : MicroCEnv) (henv : EnvTyped Γ env) :
    ∀ (e : MicroCExpr) (t : CType) (r : Bool), exprTy Γ e = some (t, r) →
      e.definedOn Γ = true → ∃ v, evalTypedExpr Γ env e = some v
  | .litInt _, _, _, _, _ => ⟨_, rfl⟩
  | .litU32 _, _, _, _, _ => ⟨_, rfl⟩
  | .litBool _, _, _, _, _ => ⟨_, rfl⟩
  | .varRef _, _, _, _, _ => ⟨_, rfl⟩
  | .binOp op l r, t, rr, hty, hd => by
    simp only [MicroCExpr.definedOn, Bool.and_eq_true] at hd
    obtain ⟨⟨hdl, hdr⟩, hop⟩ := hd
    simp only [exprTy] at hty
    split at hty
    · rename_i tl vl tr vr hl hr
      split at hty
      · rename_i htlr; subst htlr
        obtain ⟨v1, h1⟩ := evalTypedExpr_definedOn Γ env henv l tl vl hl hdl
        obtain ⟨v2, h2⟩ := evalTypedExpr_definedOn Γ env henv r tl vr hr hdr
        rw [hl] at hop
        simp only [evalTypedExpr, h1, h2, hl]
        exact binOp_defined op l r tl vl vr t rr hty hop v1 v2
          (evalTypedExpr_typed Γ env henv l tl vl v1 hl h1)
          (evalTypedExpr_typed Γ env henv r tl vr v2 hr h2)
          (fun n hn => by subst hn; simp only [evalTypedExpr, Option.some.injEq] at h2; exact h2.symm)
      · simp at hty
    · simp at hty
  | .unaryOp op e, t, rr, hty, hd => by
    simp only [exprTy] at hty
    split at hty
    · rename_i te ve he
      split at hty
      · simp at hty
      · have hde : e.definedOn Γ = true := by
          cases op <;> simp_all [MicroCExpr.definedOn]
        obtain ⟨v1, h1⟩ := evalTypedExpr_definedOn Γ env henv e te ve he hde
        have hv1 := evalTypedExpr_typed Γ env henv e te ve v1 he h1
        simp only [evalTypedExpr, h1, he]
        cases te <;> cases v1 <;> simp only [CType.HasValue] at hv1 <;>
          cases op <;> simp_all [unaryOpTy, tyUnaryOp, evalMicroCUnaryOp_uint32,
            evalMicroCUnaryOp_int64, MicroCExpr.definedOn]
    · simp at hty
  | .powCall _ _, _, _, _, hd => by simp [MicroCExpr.definedOn] at hd
  | .arrayAccess _ _, _, _, _, hd => by simp [MicroCExpr.definedOn] at hd

private theorem evalTyped_typed_step (Γ : CDecls) (fuel : Nat)
    (ihf : ∀ fuel' < fuel, ∀ (b : Bool) (s : MicroCStmt) (env env' : MicroCEnv) (oc : Outcome),
      EnvTyped Γ env → stmtTy Γ b s = true → evalTyped fuel' Γ env s = some (oc, env') →
      EnvTyped Γ env') :
    ∀ (s : MicroCStmt) (b : Bool) (env env' : MicroCEnv) (oc : Outcome),
      EnvTyped Γ env → stmtTy Γ b s = true → evalTyped fuel Γ env s = some (oc, env') →
      EnvTyped Γ env' := by
  intro s
  induction s with
  | skip | break_ | continue_ =>
    intro b env env' oc henv _ h
    simp only [evalTyped, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact henv
  | assign x e =>
    intro b env env' oc henv hs h
    simp only [stmtTy] at hs
    cases hx : Γ.lookup x with
    | none => simp [hx] at hs
    | some t =>
      cases he : exprTy Γ e with
      | none => simp [hx, he] at hs
      | some p =>
        obtain ⟨t', r⟩ := p
        simp only [hx, he, Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨⟨rfl, -⟩, -⟩ := hs
        simp only [evalTyped] at h
        split at h
        · rename_i v hv
          simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
          exact henv.update hx (evalTypedExpr_typed Γ env henv e t r v he hv)
        · simp at h
  | seq s1 s2 ih1 ih2 =>
    intro b env env' oc henv hs h
    simp only [stmtTy, Bool.and_eq_true] at hs
    simp only [evalTyped] at h
    split at h
    · rename_i env1 h1
      exact ih2 b env1 env' oc (ih1 b env env1 .normal henv hs.1.2 h1) hs.2 h
    · rename_i r hr
      exact ih1 b env env' oc henv hs.1.2 h
  | ite c t e iht ihe =>
    intro b env env' oc henv hs h
    simp only [stmtTy, Bool.and_eq_true] at hs
    simp only [evalTyped] at h
    split at h
    · exact iht b env env' oc henv hs.1.2 h
    · exact ihe b env env' oc henv hs.2 h
    · simp at h
  | while_ c body ihb =>
    intro b env env' oc henv hs h
    have hs' := hs
    simp only [stmtTy, Bool.and_eq_true] at hs'
    cases fuel with
    | zero =>
      simp only [evalTyped, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact henv
    | succ n =>
      simp only [evalTyped] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact henv
      · split at h
        · rename_i env1 h1
          exact ihf n (Nat.lt_succ_self n) b _ env1 env' oc
            (ihf n (Nat.lt_succ_self n) true body env env1 .normal henv hs'.2 h1) hs h
        · rename_i env1 h1
          exact ihf n (Nat.lt_succ_self n) b _ env1 env' oc
            (ihf n (Nat.lt_succ_self n) true body env env1 .continue_ henv hs'.2 h1) hs h
        · rename_i env1 h1
          simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
          exact ihf n (Nat.lt_succ_self n) true body env env1 .break_ henv hs'.2 h1
        · rename_i rv env1 h1
          simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
          exact ihf n (Nat.lt_succ_self n) true body env env1 _ henv hs'.2 h1
        · rename_i env1 h1
          simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
          exact ihf n (Nat.lt_succ_self n) true body env env1 .outOfFuel henv hs'.2 h1
        · simp at h
      · simp at h
  | return_ _ => intro b env env' oc _ hs _; simp [stmtTy] at hs
  | store _ _ _ => intro b env env' oc _ hs _; simp [stmtTy] at hs
  | load _ _ _ => intro b env env' oc _ hs _; simp [stmtTy] at hs
  | call _ _ _ => intro b env env' oc _ hs _; simp [stmtTy] at hs

/-- Running a well-typed body from its declarations leaves every variable with a value of its
    declared type: `uint32_t` in `[0, 2^32)`, `int64_t` in `[-2^63, 2^63)`, `bool` a boolean. -/
theorem evalTyped_preserves_types (Γ : CDecls) (s : MicroCStmt) (h : WellTyped Γ s)
    (fuel : Nat) (oc : Outcome) (env' : MicroCEnv)
    (hrun : evalTyped fuel Γ (typedDefault Γ) s = some (oc, env')) : EnvTyped Γ env' :=
  Nat.strong_induction_on (p := fun fuel => ∀ (b : Bool) (s : MicroCStmt) (env env' : MicroCEnv)
      (oc : Outcome), EnvTyped Γ env → stmtTy Γ b s = true → evalTyped fuel Γ env s = some (oc, env') →
      EnvTyped Γ env') fuel
    (fun fuel ihf b s => evalTyped_typed_step Γ fuel ihf s b) false s _ env' oc
    (typedDefault_typed Γ) h.2.1 hrun

/-! ## Non-Vacuity -/

private def exDecls : CDecls := [("x", .u32), ("y", .i64)]

-- `0u - 1u` wraps to 4294967295, and widening keeps the value.
#guard (evalTyped 1 exDecls (typedDefault exDecls)
    (.seq (.assign "x" (.binOp .sub (.litU32 0) (.litU32 1)))
      (.assign "y" (.unaryOp .widen32to64 (.varRef "x"))))).map (fun r => (r.2 "x", r.2 "y")) ==
  some (.int 4294967295, .int 4294967295)

-- `INT64_MAX + 1` is undefined, so the typed semantics stops.
#guard (evalTyped 1 exDecls (typedDefault exDecls)
    (.seq (.assign "y" (.litInt 9223372036854775807))
      (.assign "y" (.binOp .add (.varRef "y") (.litInt 1))))).isNone

-- `power(y, 62)` at `y = 2` fits in `int64_t`; `power(y, 63)` does not.
#guard (evalTyped 1 exDecls (typedDefault exDecls)
    (.seq (.assign "y" (.litInt 2)) (.assign "y" (.binOp .add (.powCall (.varRef "y") 62) (.litInt 0))))).map
  (fun r => r.2 "y") == some (.int 4611686018427387904)
#guard (evalTyped 1 exDecls (typedDefault exDecls)
    (.seq (.assign "y" (.litInt 2)) (.assign "y" (.binOp .add (.powCall (.varRef "y") 63) (.litInt 0))))).isNone

end TrustLean
