/-
  Trust-Lean v3.1 — Unsigned Simulation
  N19.4: `evalMicroC_uint32` is a `UInt32` semantics at statement level.

  `evalS32` runs a statement on `uint32_t` and `bool` values with Lean's `UInt32` operations:
  `+ - *` and negation wrap modulo 2^32, `&&& ||| ^^^` act on the bits, and a shift is defined
  only for a count below 32. On every statement of `U32Subset`, `evalMicroC_uint32` started from
  the encoded store equals `evalS32` encoded, at every fuel, with no overflow side condition.
  `stmtToMicroC_correct_uint32` and `stmtToMicroC_correct_uint64` (Simulation.lean) carry a Core
  statement to MicroC under the same operators.
-/
import TrustLean.MicroC.UnsignedAgreement
import TrustLean.MicroC.TypedEval

set_option autoImplicit false

namespace TrustLean

/-! ## Values, Stores and Outcomes -/

/-- A `uint32_t` or a `bool`. -/
inductive V32 where
  | w : UInt32 → V32
  | b : Bool → V32
  deriving DecidableEq, Repr

/-- The `Value` the other MicroC evaluators hold for a `V32`. -/
def V32.lift : V32 → Value
  | .w x => .int x.toNat
  | .b c => .bool c

@[simp] theorem V32.lift_w (x : UInt32) : (V32.w x).lift = .int x.toNat := rfl
@[simp] theorem V32.lift_b (c : Bool) : (V32.b c).lift = .bool c := rfl

abbrev Store32 := String → V32

def Store32.update (ρ : Store32) (x : String) (v : V32) : Store32 :=
  fun n => if n = x then v else ρ n

inductive Outcome32 where
  | normal
  | break_
  | continue_
  | return_ : Option V32 → Outcome32
  | outOfFuel
  deriving DecidableEq, Repr

def Outcome32.lift : Outcome32 → Outcome
  | .normal => .normal
  | .break_ => .break_
  | .continue_ => .continue_
  | .return_ v => .return_ (v.map V32.lift)
  | .outOfFuel => .outOfFuel

def liftResult (r : Outcome32 × Store32) : Outcome × MicroCEnv := (r.1.lift, V32.lift ∘ r.2)

/-- The cell `name[i]`, under the key `evalMicroC_uint32` gives it. -/
def cell32 (name : String) (i : UInt32) : String := name ++ "[" ++ toString (i.toNat : Int) ++ "]"

/-! ## Operators -/

def binOpS32 : MicroCBinOp → V32 → V32 → Option V32
  | .add, .w a, .w b => some (.w (a + b))
  | .sub, .w a, .w b => some (.w (a - b))
  | .mul, .w a, .w b => some (.w (a * b))
  | .eqOp, .w a, .w b => some (.b (a == b))
  | .ltOp, .w a, .w b => some (.b (decide (a < b)))
  | .land, .b a, .b b => some (.b (a && b))
  | .lor, .b a, .b b => some (.b (a || b))
  | .band, .w a, .w b => some (.w (a &&& b))
  | .bor, .w a, .w b => some (.w (a ||| b))
  | .bxor, .w a, .w b => some (.w (a ^^^ b))
  | .bshl, .w a, .w b => if b < 32 then some (.w (a <<< b)) else none
  | .bshr, .w a, .w b => if b < 32 then some (.w (a >>> b)) else none
  | _, _, _ => none

def unaryOpS32 : MicroCUnaryOp → V32 → Option V32
  | .neg, .w a => some (.w (-a))
  | .lnot, .b b => some (.b (!b))
  | _, _ => none

/-! ## Evaluator -/

def evalS32Expr (ρ : Store32) : MicroCExpr → Option V32
  | .litInt n => some (.w (UInt32.ofNat n.toNat))
  | .litU32 n => some (.w n)
  | .litBool b => some (.b b)
  | .varRef x => some (ρ x)
  | .binOp op l r =>
    match evalS32Expr ρ l, evalS32Expr ρ r with
    | some a, some b => binOpS32 op a b
    | _, _ => none
  | .unaryOp op e =>
    match evalS32Expr ρ e with
    | some a => unaryOpS32 op a
    | none => none
  | .powCall _ _ => none
  | .arrayAccess base idx =>
    match base with
    | .varRef name =>
      match evalS32Expr ρ idx with
      | some (.w i) => some (ρ (cell32 name i))
      | _ => none
    | _ => none

abbrev Run32 := Store32 → MicroCStmt → Option (Outcome32 × Store32)

/-- A statement at one fuel level, where `loop` runs a statement one level down and is `none` at
    fuel 0. Structural in the statement, so the kernel evaluates it. -/
def evalS32At (loop : Option Run32) : Store32 → MicroCStmt → Option (Outcome32 × Store32)
  | ρ, .skip => some (.normal, ρ)
  | ρ, .break_ => some (.break_, ρ)
  | ρ, .continue_ => some (.continue_, ρ)
  | ρ, .return_ none => some (.return_ none, ρ)
  | ρ, .return_ (some e) =>
    match evalS32Expr ρ e with
    | some v => some (.return_ (some v), ρ)
    | none => none
  | ρ, .assign x e =>
    match evalS32Expr ρ e with
    | some v => some (.normal, ρ.update x v)
    | none => none
  | ρ, .store base idx val =>
    match getMicroCArrayName' base, evalS32Expr ρ idx, evalS32Expr ρ val with
    | some name, some (.w i), some v => some (.normal, ρ.update (cell32 name i) v)
    | _, _, _ => none
  | ρ, .load x base idx =>
    match getMicroCArrayName' base, evalS32Expr ρ idx with
    | some name, some (.w i) => some (.normal, ρ.update x (ρ (cell32 name i)))
    | _, _ => none
  | _, .call _ _ _ => none
  | ρ, .seq s1 s2 =>
    match evalS32At loop ρ s1 with
    | some (.normal, ρ') => evalS32At loop ρ' s2
    | other => other
  | ρ, .ite c t e =>
    match evalS32Expr ρ c with
    | some (.b true) => evalS32At loop ρ t
    | some (.b false) => evalS32At loop ρ e
    | _ => none
  | ρ, .while_ c body =>
    match loop with
    | none => some (.outOfFuel, ρ)
    | some run =>
      match evalS32Expr ρ c with
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

/-- Run a statement on `uint32_t` and `bool` values; fuel bounds the loop depth as in
    `evalMicroC_uint32`. -/
def evalS32 : Nat → Store32 → MicroCStmt → Option (Outcome32 × Store32)
  | 0 => evalS32At none
  | n + 1 => evalS32At (some (evalS32 n))

/-! ## The Subset -/

/-- Literals in `[0, 2^32)`; no cast and no `power`. -/
def MicroCExpr.u32Ok : MicroCExpr → Bool
  | .litInt n => decide (0 ≤ n ∧ n < 2 ^ 32)
  | .litU32 _ | .litBool _ | .varRef _ => true
  | .binOp _ l r => l.u32Ok && r.u32Ok
  | .unaryOp .neg e | .unaryOp .lnot e => e.u32Ok
  | .unaryOp _ _ | .powCall _ _ => false
  | .arrayAccess _ idx => idx.u32Ok

def MicroCStmt.u32Ok : MicroCStmt → Bool
  | .assign _ e => e.u32Ok
  | .store _ idx val => idx.u32Ok && val.u32Ok
  | .load _ _ idx => idx.u32Ok
  | .seq s1 s2 => s1.u32Ok && s2.u32Ok
  | .ite c t e => c.u32Ok && t.u32Ok && e.u32Ok
  | .while_ c b => c.u32Ok && b.u32Ok
  | .return_ (some e) => e.u32Ok
  | .return_ none | .call _ _ _ | .skip | .break_ | .continue_ => true

/-- Every expression of `s` is built from `uint32_t` literals, variables, array cells and the
    operators `evalS32` defines. -/
def U32Subset (s : MicroCStmt) : Prop := s.u32Ok = true

instance (s : MicroCStmt) : Decidable (U32Subset s) := inferInstanceAs (Decidable (_ = _))

/-! ## Operator Agreement -/

private theorem wrap_natCast (n : Nat) : wrapUInt32 (n : Int) = ((n % 2 ^ 32 : Nat) : Int) := by
  simp only [wrapUInt32, wrapWidth]; omega

private theorem wrap_natCast_of_lt (n : Nat) (h : n < 2 ^ 32) : wrapUInt32 (n : Int) = n := by
  rw [wrap_natCast, Nat.mod_eq_of_lt h]

theorem binOpS32_lift (op : MicroCBinOp) (a b : V32) :
    evalMicroCBinOp_uint32 op a.lift b.lift = (binOpS32 op a b).map V32.lift := by
  cases op <;> cases a <;> cases b <;> rename_i x y <;>
    simp only [evalMicroCBinOp_uint32, binOpS32, V32.lift, Option.map_some, Option.map_none]
  case add.w.w =>
    simp only [addUInt32, UInt32.toNat_add]; rw [← Int.natCast_add, wrap_natCast]
  case sub.w.w =>
    have hx := x.toNat_lt; have hy := y.toNat_lt
    simp only [subUInt32, UInt32.toNat_sub, wrapUInt32, wrapWidth, Option.some.injEq,
      Value.int.injEq]; omega
  case mul.w.w =>
    simp only [mulUInt32, UInt32.toNat_mul]; rw [← Int.natCast_mul, wrap_natCast]
  case eqOp.w.w =>
    congr 2
    by_cases h : x = y
    · subst h; simp
    · have : x.toNat ≠ y.toNat := fun e => h (UInt32.toNat_inj.mp e)
      simp [h, this]
  case ltOp.w.w => simp [UInt32.lt_iff_toNat_lt]
  case band.w.w =>
    rw [UInt32.toNat_and]
    exact congrArg (some ∘ Value.int) (wrap_natCast_of_lt _ (Nat.and_lt_two_pow _ y.toNat_lt))
  case bor.w.w =>
    rw [UInt32.toNat_or]
    exact congrArg (some ∘ Value.int)
      (wrap_natCast_of_lt _ (Nat.or_lt_two_pow x.toNat_lt y.toNat_lt))
  case bxor.w.w =>
    rw [UInt32.toNat_xor]
    exact congrArg (some ∘ Value.int)
      (wrap_natCast_of_lt _ (Nat.xor_lt_two_pow x.toNat_lt y.toNat_lt))
  case bshl.w.w =>
    have hlt : y < 32 ↔ y.toNat < 32 := UInt32.lt_iff_toNat_lt
    by_cases h : y.toNat < 32
    · have h' : y < 32 := hlt.mpr h
      simp only [h', ↓reduceIte, Option.map_some, V32.lift, UInt32.toNat_shiftLeft,
        Nat.mod_eq_of_lt h]
      rw [if_pos ⟨by omega, by omega⟩, Int.toNat_natCast]
      exact congrArg (some ∘ Value.int) (wrap_natCast _)
    · have h' : ¬ y < 32 := fun e => h (hlt.mp e)
      simp only [h', ↓reduceIte, Option.map_none]
      rw [if_neg (by omega)]
  case bshr.w.w =>
    have hlt : y < 32 ↔ y.toNat < 32 := UInt32.lt_iff_toNat_lt
    by_cases h : y.toNat < 32
    · have h' : y < 32 := hlt.mpr h
      simp only [h', ↓reduceIte, Option.map_some, V32.lift, UInt32.toNat_shiftRight,
        Nat.mod_eq_of_lt h]
      rw [if_pos ⟨by omega, by omega⟩, Int.toNat_natCast]
      exact congrArg (some ∘ Value.int) (wrap_natCast_of_lt _
        (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.toNat_lt))
    · have h' : ¬ y < 32 := fun e => h (hlt.mp e)
      simp only [h', ↓reduceIte, Option.map_none]
      rw [if_neg (by omega)]

theorem unaryOpS32_lift (op : MicroCUnaryOp) (a : V32) (h : op = .neg ∨ op = .lnot) :
    evalMicroCUnaryOp_uint32 op a.lift = (unaryOpS32 op a).map V32.lift := by
  rcases h with rfl | rfl <;> cases a <;> rename_i x <;>
    simp only [evalMicroCUnaryOp_uint32, unaryOpS32, V32.lift, Option.map_some, Option.map_none]
  have hx := x.toNat_lt
  simp only [UInt32.toNat_neg, UInt32.size, wrapUInt32, wrapWidth, Option.some.injEq,
    Value.int.injEq]; omega

/-! ## Expressions -/

theorem evalS32Expr_lift (ρ : Store32) :
    ∀ (e : MicroCExpr), e.u32Ok = true →
      evalMicroCExpr_uint32 (V32.lift ∘ ρ) e = (evalS32Expr ρ e).map V32.lift
  | .litInt n, h => by
    simp only [MicroCExpr.u32Ok, decide_eq_true_eq] at h
    simp only [evalMicroCExpr_uint32, evalS32Expr, Option.map_some, V32.lift,
      UInt32.toNat_ofNat_of_lt' (show n.toNat < UInt32.size by simp only [UInt32.size]; omega)]
    congr 2; omega
  | .litU32 _, _ => rfl
  | .litBool _, _ => rfl
  | .varRef _, _ => rfl
  | .binOp op l r, h => by
    simp only [MicroCExpr.u32Ok, Bool.and_eq_true] at h
    simp only [evalMicroCExpr_uint32, evalS32Expr, evalS32Expr_lift ρ l h.1,
      evalS32Expr_lift ρ r h.2]
    cases evalS32Expr ρ l <;> cases evalS32Expr ρ r <;> simp [binOpS32_lift]
  | .unaryOp op e, h => by
    have hop : op = .neg ∨ op = .lnot := by cases op <;> simp_all [MicroCExpr.u32Ok]
    have he : e.u32Ok = true := by rcases hop with rfl | rfl <;> simpa [MicroCExpr.u32Ok] using h
    simp only [evalMicroCExpr_uint32, evalS32Expr, evalS32Expr_lift ρ e he]
    cases evalS32Expr ρ e <;> simp [unaryOpS32_lift _ _ hop]
  | .powCall _ _, h => by simp [MicroCExpr.u32Ok] at h
  | .arrayAccess base idx, h => by
    simp only [MicroCExpr.u32Ok] at h
    simp only [evalMicroCExpr_uint32, evalS32Expr]
    cases base <;> try rfl
    simp only [evalS32Expr_lift ρ idx h]
    rcases evalS32Expr ρ idx with _ | _ | _ <;> rfl

/-! ## Statements -/

theorem lift_update (ρ : Store32) (x : String) (v : V32) :
    MicroCEnv.update (V32.lift ∘ ρ) x v.lift = V32.lift ∘ ρ.update x v := by
  funext n; simp only [MicroCEnv.update, Store32.update, Function.comp]; split <;> rfl

private def loopOf : Nat → Option Run32
  | 0 => none
  | n + 1 => some (evalS32 n)

private theorem evalS32_eq_At (fuel : Nat) : evalS32 fuel = evalS32At (loopOf fuel) := by
  cases fuel <;> rfl

private theorem evalS32_step (fuel : Nat)
    (ihf : ∀ n < fuel, ∀ (s : MicroCStmt) (ρ : Store32), s.u32Ok = true →
      evalMicroC_uint32 n (V32.lift ∘ ρ) s = (evalS32 n ρ s).map liftResult) :
    ∀ (s : MicroCStmt) (ρ : Store32), s.u32Ok = true →
      evalMicroC_uint32 fuel (V32.lift ∘ ρ) s = (evalS32At (loopOf fuel) ρ s).map liftResult := by
  intro s
  induction s with
  | skip | break_ | continue_ | call =>
    intro ρ _; simp [evalMicroC_uint32, evalS32At, liftResult, Outcome32.lift]
  | return_ re =>
    intro ρ hs
    cases re with
    | none => simp [evalMicroC_uint32, evalS32At, liftResult, Outcome32.lift]
    | some e =>
      simp only [MicroCStmt.u32Ok] at hs
      simp only [evalMicroC_uint32, evalS32At, evalS32Expr_lift ρ e hs]
      cases evalS32Expr ρ e <;> simp [liftResult, Outcome32.lift]
  | assign x e =>
    intro ρ hs
    simp only [MicroCStmt.u32Ok] at hs
    simp only [evalMicroC_uint32, evalS32At, evalS32Expr_lift ρ e hs]
    cases evalS32Expr ρ e <;> simp [liftResult, Outcome32.lift, lift_update]
  | store base idx val =>
    intro ρ hs
    simp only [MicroCStmt.u32Ok, Bool.and_eq_true] at hs
    simp only [evalMicroC_uint32, evalS32At, evalS32Expr_lift ρ idx hs.1,
      evalS32Expr_lift ρ val hs.2]
    cases getMicroCArrayName' base <;> rcases evalS32Expr ρ idx with _ | _ | _ <;>
      cases evalS32Expr ρ val <;> simp [liftResult, Outcome32.lift, lift_update, cell32]
  | load x base idx =>
    intro ρ hs
    simp only [MicroCStmt.u32Ok] at hs
    simp only [evalMicroC_uint32, evalS32At, evalS32Expr_lift ρ idx hs]
    cases getMicroCArrayName' base <;> rcases evalS32Expr ρ idx with _ | _ | _ <;>
      simp [liftResult, Outcome32.lift, lift_update, cell32]
  | seq s1 s2 ih1 ih2 =>
    intro ρ hs
    simp only [MicroCStmt.u32Ok, Bool.and_eq_true] at hs
    simp only [evalMicroC_uint32, evalS32At, ih1 ρ hs.1]
    rcases evalS32At (loopOf fuel) ρ s1 with _ | ⟨oc, ρ'⟩
    · rfl
    · cases oc <;> simp [liftResult, Outcome32.lift, ih2 ρ' hs.2]
  | ite c t e iht ihe =>
    intro ρ hs
    simp only [MicroCStmt.u32Ok, Bool.and_eq_true] at hs
    simp only [evalMicroC_uint32, evalS32At, evalS32Expr_lift ρ c hs.1.1]
    rcases evalS32Expr ρ c with _ | _ | (_ | _)
    · rfl
    · rfl
    · exact ihe ρ hs.2
    · exact iht ρ hs.1.2
  | while_ c body _ =>
    intro ρ hs
    have hs' := hs
    simp only [MicroCStmt.u32Ok, Bool.and_eq_true] at hs'
    cases fuel with
    | zero => simp [evalMicroC_uint32, evalS32At, loopOf, liftResult, Outcome32.lift]
    | succ n =>
      have hb := ihf n (Nat.lt_succ_self n) body
      have hw := ihf n (Nat.lt_succ_self n) (.while_ c body)
      simp only [evalMicroC_uint32, evalS32At, loopOf, evalS32Expr_lift ρ c hs'.1]
      rcases evalS32Expr ρ c with _ | _ | (_ | _)
      · rfl
      · rfl
      · simp [V32.lift, liftResult, Outcome32.lift]
      · simp only [Option.map_some, V32.lift, hb ρ hs'.2]
        rcases evalS32 n ρ body with _ | ⟨oc, ρ'⟩
        · rfl
        · cases oc <;> simp [liftResult, Outcome32.lift, hw ρ' hs]

/-- On `U32Subset`, `evalMicroC_uint32` is `evalS32`: every value wraps where `UInt32` wraps,
    at every fuel, with no range hypothesis on any intermediate value. -/
theorem evalMicroC_uint32_eq_evalS32 (fuel : Nat) (ρ : Store32) (s : MicroCStmt)
    (hs : U32Subset s) :
    evalMicroC_uint32 fuel (V32.lift ∘ ρ) s = (evalS32 fuel ρ s).map liftResult := by
  rw [evalS32_eq_At]
  exact Nat.strong_induction_on (p := fun fuel => ∀ (s : MicroCStmt) (ρ : Store32),
      s.u32Ok = true → evalMicroC_uint32 fuel (V32.lift ∘ ρ) s =
        (evalS32At (loopOf fuel) ρ s).map liftResult) fuel
    (fun fuel ihf => evalS32_step fuel fun n hn s ρ h => by
      rw [evalS32_eq_At]; exact ihf n hn s ρ h) s ρ hs

/-! ## Typed Programs -/

theorem MicroCExpr.u32Ok_of_inU32Subset :
    ∀ (e : MicroCExpr), e.inU32Subset = true → e.u32Ok = true
  | .litU32 _, _ | .litBool _, _ | .varRef _, _ => rfl
  | .binOp _ l r, h => by
    simp only [MicroCExpr.inU32Subset, Bool.and_eq_true] at h
    simp [MicroCExpr.u32Ok, u32Ok_of_inU32Subset l h.1, u32Ok_of_inU32Subset r h.2]
  | .unaryOp op e, h => by
    cases op <;> simp only [MicroCExpr.inU32Subset, reduceCtorEq] at h <;>
      simp [MicroCExpr.u32Ok, u32Ok_of_inU32Subset e h]
  | .litInt _, h | .powCall _ _, h | .arrayAccess _ _, h => by simp [MicroCExpr.inU32Subset] at h

theorem MicroCStmt.u32Ok_of_inU32Subset :
    ∀ (s : MicroCStmt), s.inU32Subset = true → s.u32Ok = true
  | .skip, _ | .break_, _ | .continue_, _ => rfl
  | .assign _ e, h => MicroCExpr.u32Ok_of_inU32Subset e h
  | .seq s1 s2, h => by
    simp only [MicroCStmt.inU32Subset, Bool.and_eq_true] at h
    simp [MicroCStmt.u32Ok, u32Ok_of_inU32Subset s1 h.1, u32Ok_of_inU32Subset s2 h.2]
  | .ite c t e, h => by
    simp only [MicroCStmt.inU32Subset, Bool.and_eq_true] at h
    simp [MicroCStmt.u32Ok, MicroCExpr.u32Ok_of_inU32Subset c h.1.1, u32Ok_of_inU32Subset t h.1.2,
      u32Ok_of_inU32Subset e h.2]
  | .while_ c b, h => by
    simp only [MicroCStmt.inU32Subset, Bool.and_eq_true] at h
    simp [MicroCStmt.u32Ok, MicroCExpr.u32Ok_of_inU32Subset c h.1, u32Ok_of_inU32Subset b h.2]
  | .store _ _ _, h | .load _ _ _, h | .call _ _ _, h | .return_ _, h => by
    simp [MicroCStmt.inU32Subset] at h

/-- A well-typed `uint32_t` program, whose printed C `CheckTypedC` compiles and runs, computes
    what `evalS32` computes. -/
theorem evalTyped_eq_evalS32 (Γ : CDecls) (s : MicroCStmt) (h : WellTypedU32 Γ s) (fuel : Nat)
    (ρ : Store32) : evalTyped fuel Γ (V32.lift ∘ ρ) s = (evalS32 fuel ρ s).map liftResult := by
  rw [evalTyped_eq_evalMicroC_uint32 Γ s h]
  exact evalMicroC_uint32_eq_evalS32 fuel ρ s (MicroCStmt.u32Ok_of_inU32Subset s h.2.2)

/-! ## Non-Vacuity: a Ring-Buffer Push Across the 2^32 Wrap -/

/-- `occ = tail - head; if (occ < cap) { buf[tail & (cap - 1)] = v; tail = tail + 1; ok = true; }
    else { ok = false; }` -/
def pushK : MicroCStmt :=
  .seq (.assign "occ" (.binOp .sub (.varRef "tail") (.varRef "head")))
   (.ite (.binOp .ltOp (.varRef "occ") (.varRef "cap"))
     (.seq (.store (.varRef "buf") (.binOp .band (.varRef "tail") (.binOp .sub (.varRef "cap")
         (.litInt 1))) (.varRef "v"))
       (.seq (.assign "tail" (.binOp .add (.varRef "tail") (.litInt 1)))
             (.assign "ok" (.litBool true))))
     (.assign "ok" (.litBool false)))

/-- `head = 2^32 - 2`, `tail = 2^32 - 1`, `cap = 8`, `v = 42`, `ok = false`. -/
def pushStore : Store32 := fun x =>
  if x = "head" then .w 4294967294 else if x = "tail" then .w 4294967295
  else if x = "cap" then .w 8 else if x = "v" then .w 42 else if x = "ok" then .b false else .w 0

theorem pushK_u32Subset : U32Subset pushK := by decide

/-- `tail` wraps to 0 while the occupancy stays 1, as `probe.c` prints under `uint32_t`
    declarations: `tail=0 occ=1 ok=1 buf[7]=42`. -/
theorem evalMicroC_uint32_pushK :
    (evalMicroC_uint32 1 (V32.lift ∘ pushStore) pushK).map
      (fun r => (r.2 "tail", r.2 "occ", r.2 "ok", r.2 "buf[7]")) =
    some (.int 0, .int 1, .bool true, .int 42) := by
  rw [evalMicroC_uint32_eq_evalS32 1 pushStore pushK pushK_u32Subset]
  decide

/-- The same statement for the unbounded `evalMicroC` is false: it leaves `tail = 4294967296`. -/
theorem evalMicroC_ne_evalS32 :
    ¬ ∀ (fuel : Nat) (ρ : Store32) (s : MicroCStmt), U32Subset s →
      evalMicroC fuel (V32.lift ∘ ρ) s = (evalS32 fuel ρ s).map liftResult := by
  intro h
  have := congrArg (Option.map fun r => r.2 "tail") (h 1 pushStore pushK pushK_u32Subset)
  revert this
  simp [evalMicroC, pushK, pushStore, V32.lift]
  decide

/-- The per-operation agreement of `UnsignedAgreement` needs its result in range, which fails at
    the wrap `pushK` takes: `4294967295 + 1`. -/
theorem not_inUInt32Range_wrap : ¬ InUInt32Range (4294967295 + 1) := by
  unfold InUInt32Range; decide

end TrustLean
